%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relational types + Mereology + Existential dependence + Inherence + IntrinsicMoments
% ExternallyDependentModes + Relators
% July 2019
% Daniele Porello and Claudenir M. Fonseca
% Contributions from  Joao Paulo A. Almeida, Nicola Guarino, Giancarlo Guizzardi

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Proved consistent Darwin 1.4.4.


% This file includes:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Formal characterization of Endurant Types in UFO
% Joao Paulo A. Almeida, Apr-2018
% Contributions from Giancarlo Guizzardi, Claudenir M. Fonseca, Daniele Porello,
% Tiago Prince Sales, Alessander B. Benevides

% Use theorem provers at http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP


% Joao Paulo A. Almeida, Apr-2018
% Contributions from Giancarlo Guizzardi, Claudenir M. Fonseca, Daniele Porello,
% Tiago Prince Sales, Alessander B. Benevides

% Use theorem provers at http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTPTP
% Proved also consistent Darwin 1.4.4.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%



%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning instantiation and specialization

% Types are those entities that are possibly instantiated
fof(ax_dtype_, axiom, (
    ![X] : (type_(X) <=> (~world(X) & ?[W,Y,Z] : (world(W) & (iof(Y,X,W) | iofr(Y,Z,X,W))))
    ))).

% Individuals are those entities that are necessarily not instantiated
fof(ax_dindividual, axiom, (
    ![X] : (individual(X) <=> (~world(X) & ![W] : (world(W) => ~?[Y] : (iof(Y,X,W)))) )
    )).

% We are only concerned with first-order types
fof(ax_twolevel, axiom, (
    ![X,Y,W] : (iof(X,Y,W) => (individual(X) & type_(Y) & world(W)))
    )).

% Specialization definition
fof(ax_dspecialization, axiom, (
    ![T1,T2] :
    (specializes(T1,T2) <=> (type_(T1)&type_(T2) &
            ![W]: (world(W)=> ![E]:(iof(E,T1,W) => iof(E,T2,W)))))
    )).

% Whenever two types have a common instance, they must share a supertype or a subtype for this instance
fof(ax_nondisjointSameTaxonomy, axiom, (
    ![T1,T2]: (![X,W]: ((iof(X,T1,W)&iof(X,T2,W)&~specializes(T1,T2)&~specializes(T2,T1))=>
        (
            (?[T3]: (specializes(T1,T3)&specializes(T2,T3)&iof(X,T3,W)))|
            (?[T3]: (specializes(T3,T1)&specializes(T3,T2)&iof(X,T3,W)))
        )
        ))
)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning rigidity

% Definition of rigid type
fof(ax_drigid, axiom, (
    ![T]: (rigid(T)<=>(type_(T) &
                    (![X]: ((?[W]: (world(W) & iof(X,T,W))) => (![W2]: (world(W2)=>iof(X,T,W2)))))))
)).

% Definition of antirigid type
fof(ax_dantirigid, axiom, (
    ![T]: (antirigid(T)<=>(type_(T) &
                    (![X]: ((?[W]: (world(W) & iof(X,T,W))) => (?[W2]: (world(W2)&~iof(X,T,W2)))))))
)).

% Implicit definition of semirigid type
fof(ax_semirigid, axiom, (
    ![T]: (semirigid(T)<=>(type_(T) &
                    ~antirigid(T) & ~rigid(T)))
)).

%%%%%%%%%%%%%%%%%%%%%%%% Concerning sortality

% Every *individual* necessarily instantiates a kind  // imply kinds are rigid!
fof(ax_individualKindMin, axiom, (
    ![X] : (individual(X) => ?[K]:(kind(K) & ![W]: (world(W)=>iof(X,K,W))))
    )).

% Every thing instantiates at most one kind (whenever it instantiates a kind it does not
% possible instantiate a different one

fof(ax_individualKindMax, axiom, (
    ![X,K,W] : ( ( kind(K) & iof(X,K,W)) =>
                (~?[Z,W2]: (~(Z=K) & kind(Z) & iof(X,Z,W2))) )
    )).

% Sortals definition, sortals are those types whose instances instantiate the same kind
fof(ax_dsortal, axiom, (
    ![T] :
    ( sortal(T) <=> (type_(T) &
                    (?[K] : (kind(K) & ![X,W]: (world(W)=>(iof(X,T,W) => iof(X,K,W) )))) ))
    )).

% A non-sortal is a type that is not a sortal

fof(ax_dnonsortal, axiom, (
    ![T] : ( nonsortal(T) <=> (type_(T) & ~sortal(T)) )
    )).


%%%%%%%%%%% Concerning the leaf elements of the taxonomy of types in UFO

% Kinds and subkinds together encompass all rigid sortals
fof(ax_kindsSubkinds, axiom, (
    ![T]: ((kind(T)|subkind(T))<=>(rigid(T)&sortal(T)))
)).

% Kind and subkind are disjoint
fof(ax_kindSubkindDisjoint, axiom, (
    ~?[T]: (kind(T)&subkind(T))
)).

% Phase and roles together encompass all antirigid sortals
fof(ax_phasesRoles, axiom, (
    ![T]: ((phase(T)|role(T))<=>(antirigid(T)&sortal(T)))
)).

% They are disjoint
fof(ax_phaseRoleDisjoint, axiom, (
    ~?[T]: (phase(T)&role(T))
)).

%%% Theorems to show that we can omit <<relatorphase>> and <<relatorrole>> as a demonstration
% (same applies to relatorsubkind, modephase, moderole, modesubkind, qualityphase, qualityrole, qualitysubkind)

% Relator phase is a phase that is applicable to relators only
fof(ax_drelatorPhase, axiom, (
    ![T]: (relatorphase(T)<=> (relatortype(T) & phase(T)))
)).

% Relator role is a role that is applicable to relators only
fof(ax_drelatorRole, axiom, (
    ![T]: (relatorrole(T)<=> (relatortype(T) & role(T)))
)).

% Semi rigid sortals are those that are semirigid and sortal
fof(ax_dsemirigidSortal, axiom, (
    ![T]: (semirigidsortal(T)<=>(semirigid(T)&sortal(T)))
)).

% Categories are those types that are rigid and non-sortals
fof(ax_dcategory, axiom, (
    ![T]: (category(T)<=>(rigid(T)&nonsortal(T)))
)).

% Mixins are those types that are semirigid and non-sortals
fof(ax_dmixin, axiom, (
    ![T]: (mixin(T)<=>(semirigid(T)&nonsortal(T)))
)).

% Phase and roles together encompass all antirigid nonsortals
fof(ax_phaseRoleMixins, axiom, (
    ![T]: ((phasemixin(T)|rolemixin(T))<=>(antirigid(T)&nonsortal(T)))
)).

% They are disjoint
fof(ax_phaseRoleMixinDisjoint, axiom, (
    ~?[T]: (phasemixin(T)&rolemixin(T))
)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%% Concerning the taxonomy of endurant (individuals)

% Endurants are individuals
fof(ax_endurantsAreIndividuals, axiom, (
    ![X]: (endurant(X)=>individual(X))
)).

% Substantials and moments together encompass endurants
fof(ax_substantialsMoments, axiom, (
    ![X]: ((substantial(X)|moment(X))<=>endurant(X))
)).

% Substantial and moment are disjoint
fof(ax_substantialMomentDisjoint, axiom, (
    ~?[X]: (substantial(X)&moment(X))
)).

% Relators and intrinsic moments together encompass moments
fof(ax_relatorsIntrinsicMoments, axiom, (
    ![X]: (moment(X)<=>(relator(X)|intrinsicmoment(X)))
)).

% Relator and intrinsic moment are disjoint
 fof(ax_relatorIntrinsicMomentDisjoint, axiom, (
    ~?[X]: (relator(X)&intrinsicmoment(X)))).

% Modes and qualities together encompass intrinsic moments
fof(ax_modesQualities, axiom, (
    ![X]: (intrinsicmoment(X)<=>(mode(X)|quality(X)))
)).

% Mode and quality are disjoint
fof(ax_modeQualityDisjoint, axiom, (
    ~?[X]: (mode(X)&quality(X))
)).

%%%%%%%%%%%%%%%%%%%%%%%%%% Taxonomy of endurant types according to the ontological nature of their instances

% Endurant types are all those types whose instances are endurants
fof(ax_dendurantType, axiom, (
    ![T]: (enduranttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>endurant(X)))))
)).

% Substantial types are all those types whose instances are substantials
fof(ax_dsubstantialType, axiom, (
    ![T]: (substantialtype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>substantial(X)))))
)).

% Moment types are all those types whose instances are moments
fof(ax_dmomentType, axiom, (
    ![T]: (momenttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>moment(X)))))
)).

% Relator types are all those types whose instances are relators
fof(ax_drelatorType, axiom, (
    ![T]: (relatortype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>relator(X)))))
)).

% Mode types are all those types whose instances are modes
fof(ax_dmodeType, axiom, (
    ![T]: (modetype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>mode(X)))))
)).

% Quality types are all those types whose instances are qualities
fof(ax_dqualityType, axiom, (
    ![T]: (qualitytype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>quality(X)))))
)).

%%% Kinds are specialized according to the ontological nature of their instances

% Substantial kinds are those kinds whose instances are substantials
fof(ax_dsubstantialKind, axiom, (
    ![T]: (substantialkind(T)<=> (substantialtype(T) & kind(T)))
)).

% Relator kinds are those kinds whose instances are relators
fof(ax_drelatorKind, axiom, (
    ![T]: (relatorkind(T) <=> (relatortype(T) & kind(T)))
)).

% Mode kinds are those kinds whose instances are modes
fof(ax_dmodeKind, axiom, (
    ![T]: (modekind(T)<=> (modetype(T) & kind(T)))
)).

% Quality kinds are those kinds whose instances are relators
fof(ax_dqualityKind, axiom, (
    ![T]: (qualitykind(T)<=> (qualitytype(T) & kind(T)))
)).

% every endurant is instance of one of the specific endurant kinds
fof(ax_everyEndurantInstantiatesSpecificKind, axiom, (
    ![X]: (endurant(X) => (?[W,K]: ((substantialkind(K)|relatorkind(K)|modekind(K)|qualitykind(K))& iof(X,K,W))))
)).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relational types + Mereology + Existential dependence + Inherence + IntrinsicMoments
% ExternallyDependentModes + Relators
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Proved consistent Darwin 1.4.4.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Mereology

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


        fof(ax_part_rifl, axiom, (![X]: (part(X,X)))).

        fof(ax_part_antisymm, axiom, (![X,Y]: ((part(X,Y) & part(Y,X)) => (Y=X)))).

        fof(ax_part_trans, axiom, (![X,Y,Z]: ((part(X,Y) & part(Y,Z)) => part(X,Z)))).

        fof(ax_part_overlappin, axiom, (![X,Y]: (overlap(X,Y) <=> ?[Z]:(part(Z,X) & part(Z,Y))))).

        fof(ax_part_strong_supp, axiom, (![X,Y]: (~part(Y,X) => ?[Z]:(part(Z,Y) & ~overlap(Z,X))))).

        fof(ax_part_proper_part, axiom, (![X,Y]: (properPart(Y,X) <=> (part(Y,X) & ~part(X,Y))))).

        fof(ax_part_sum, axiom, (![Z,X,Y]: (sum(Z,X,Y) <=> ![W]:((overlap(W,Z) <=> (overlap(W,X) | overlap(W,X))))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Existential dependence
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


        fof(ax_existence, axiom, (![X]: ((type(X) | individual(X)) => thing(X)))).

        %Existence axiom.

        fof(ax_existence, axiom, (![X,W]: (ex(X,W) => (thing(X) & world(W))))).

        %existential dependence and independence

        fof(ax_existential_dependence, axiom, (![X,Y]: (ed(X,Y) <=> ![W]:(ex(X,W) => ex(Y,W))))).

        fof(ax_existential_independence, axiom, (![X,Y]: (ind(X,Y) <=> (~ed(X,Y) & ~ed(Y,X))))).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Inherence
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


        fof(ax_inherence_type, axiom, (![X,Y]: (inheresIn(X,Y) => (moment(X) & endurant(Y))))).

        fof(ax_inherence_ed, axiom, (![X,Y]: (inheresIn(X,Y) => ed(X,Y)))).

        fof(ax_inherence_irrifl, axiom, (![X]: ~inheresIn(X,X))).

        fof(ax_inherence_asymm, axiom, (![X,Y]: inheresIn(X,Y) => ~inheresIn(Y,X))).

        fof(ax_inherence_intrans, axiom, (![X,Y]: ((inheresIn(X,Y) & inheresIn(Y,Z)) => ~inheresIn(X,Z)))).

        fof(ax_inherence_unic, axiom, (![X,Y,Z]: ((inheresIn(X,Y) & inheresIn(X,Z)) => Y=Z))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Properties. Intrinsic. Extrinsic. Descriptive. Non-descriptive.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Proved consistent Darwin 1.4.4.

%Properites are types

                fof(ax_def_propertytype, axiom, (![P]: (property(P) => type_(P)))).
                fof(ax_def_intrinsicpropertytype, axiom, (![P]: (intrinsicproperty(P) => property(P)))).
                fof(ax_def_extrinsicpropertytype, axiom, (![P]: (extrinsicproperty(P) => property(P)))).
                fof(ax_def_descriptivepropertytype, axiom, (![P]: (descriptiveproperty(P) => property(P)))).
                fof(ax_def_nondescriptivepropertytype, axiom, (![P]: (nondescriptiveproperty(P) => property(P)))).


%%%%%%%%%%%%%%%%Intrinsic property.
%%Simplifying assumption: we view intrinsic properties as types which are equivalent to the inherence of intrinsic moments that are
%% not externally dependent modes. To do this, we introduce the type of "individualmomenttype", see ax_individualmomentType
%% Moreover, we may consistently view also existence as an intrinsic property.



%%Intrinsic Moment types are those types whose instances are intrinsic moments:


fof(ax_intrinsicmomentType, axiom, (
    ![T]: (intrinsicmomenttype(T)<=> (type_(T) & (![X,W]: (iof(X,T,W)=>intrinsicmoment(X))))))).


%%Individual moment types are those types whose instances are intrinsic moments that are not externally dependents modes:


fof(ax_individualmomentType, axiom, (![T]: (individualmomenttype(T) <=>
(type_(T) & (![X,W]: (iof(X,T,W)=> (intrinsicmoment(X) & ~edm(M)))))))).


%%Intrinsic proeperties are then defined by two cases:

fof(ax_def_intrinsicP_1, axiom, (![P]: (intrinsicproperty(P) <=
                (property(P) & ?[W,X]:(iof(X,P,W)) &
                (![X,W]:(iof(X,P,W) <=>
                (?[T,M]: ((individualmomenttype(T) & moment(M) & derive(P,T) & iof(M,T,W) & inheresIn(M,X)))))))))).


fof(ax_def_intrinsicP_2, axiom, (![P]: (intrinsicproperty(P) <=  (property(P) & ?[W,X]:(iof(X,P,W)) &
                                                                  (![X,W]:(iof(X,P,W) <=> ex(X,W))))))).



%%%%%%%%%%%%%%%%%Extrinsic property
%%Extrinsic properties are not intrinsic properties.

fof(ax_def_externalP, axiom, (![P]: (extrinsicproperty(P) <=> (property(P) & ~intrinsicproperty(P))))).


%%%%%%%%%%%%%%%%Descriptive properties.
%%Descriptive properties are those that are true of their instances because of the existence of an moment that inheres in the instances
%(it may be a mode, a quality, and also an externally dependent mode).


fof(ax_def_descriptiveP, axiom, (![P]: (descriptiveproperty(P) <=> (property(P) & ?[W,X]:(iof(X,P,W)) &
                                    ![X,W]: (iof(X,P,W) <=>
                                    ?[T,M]: (momenttype(T) & derive(P,T) & moment(M) & iof(M,T,W) & inheresIn(M,X))))))).

%%%%%%%%%%%%%%%%Non-descriptive properties.
fof(ax_def_nondescriptiveP, axiom, (![P]: (nondescriptiveproperty(P) <=> (property(P) & ~descriptiveproperty(P))))).

%Tests:

%ok
%fof(ax_def_test, axiom, (intrinsicproperty(p) & ~descriptiveproperty(p))).


%Ok, proved "eprover": a property which is equivalent to existence is in fact intrinsic.

fof(cj_existence_is_intrinsic, conjecture, ((property(p) & ?[W,X]:(iof(X,p,W)) & (![W,X]: (iof(X,p,W) <=> ex(X,W)))) =>
intrinsicproperty(p))).





%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relational types. Rigid, Semirigid, Essential, Non-essential, Internal, External, Descriptive, Non-descriptive.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Proved consistent Darwin 1.4.4.


%Reification of relational types. Binary relational types <x,y> :: r in world w is defined by iofr(X,Y,R,W)

fof(ax_def_relationstype, axiom, (![R]: (relation(R) => type_(R)))).
%fof(ax_def_relationstype, axiom, (~?[R]: (relation(R) & type_(R)))).  %note that from the ER2018 formalisation, everything is either a type or an individual or a world, so here we say that relations are types.
fof(ax_def_relationstype, axiom, (~?[R]: (relation(R) & individual(R)))).
fof(ax_def_relationstype, axiom, (~?[R]: (relation(R) & world(R)))).

%"Instance of" for relations, denoted by "iofr". Typing:

fof(ax_def_relations, axiom, (![X,Y,R,W] : (iofr(X,Y,R,W) => (individual(X) & individual(Y) & relation(R) & world(W))))).


% Relational types are those entities that are possibly instantiated (via iofr):

fof(ax_relationstype_, axiom, (![R] : (relation(R) <=> (~world(R) & ?[W,X,Y] : (world(W) & individual(X) & individual(Y) & iofr(X,Y,R,W)))))).


%Test with instances

%fof(ax_def_test, axiom, individual(a)).
%fof(ax_def_test, axiom, world(w)).

%fof(ax_def_test, axiom, relation(r)).

%fof(ax_def_test, axiom, iofr(a,b,r,w)).
%fof(ax_def_test, axiom, iofr(a,b,s,w)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%Derive Relation

%%The "derive" relations is a primitive relation that serves to associate a relation (or a property) with the pertinent types or relations
%% that are required for the truthmaking. It specifies what a relation or property Y is "about".

fof(ax_def_derive, axiom, (![Y,X]: (derive(Y,X) => ((relation(Y) | property(Y)) & (momenttype(X) | relation(X) | property(X)))))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%Internal and external relations

%%%%%%%%%Definition of Internal Relations: internal relations are relations that are true because of the existence of intrinsic properties
% that are true of the relata, and that are relevant to the relation (via "derivation" relation)


fof(ax_def_internalrelations, axiom,
(![R] : (internalrelation(R) <=>
(relation(R) & (?[W1,X,Y] : (world(W1) & iofr(X,Y,R,W1)) <=>
(![W2,X,Y] : (iofr(X,Y,R,W2) <=>
?[P,Q]:(intrinsicproperty(P) & (intrinsicproperty(Q) &  derive(R,P) & derive(R,Q) & (iof(X,P,W2) & iof(Y,Q,W2))))))))))).

fof(ax_def_relations, axiom, (![R] : (internalrelation(R) => relation(R)))).

%%%%%%%%%%%%Definition of External Relations:

%fof(ax_def_extenralrelations, axiom, (![R]: (externalrelation(R) <=> (relation(R) & ~internalrelation(R))))).


%Test with instance

fof(ax_def_test, axiom, internalrelation(r)).
fof(ax_def_test, axiom, externalrelation(q)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%Descriptive and non-descriptive relations:
%% Descriptive relations are those that are about
% either i) the existence of an externally dependent mode that inheres in one relatum and existentially depends on the other or
% ii) the existence of two intrinsic moment that are not externally dependent that inhere in the relata.
% We may also consistently include moments that inhere the sum of the relata, to capture the examples of Guarino, Guizzardi, Sales, ER 2018.
% E.g. "the stars Alnitak, Alnilam, Mintaka form the constellation Orion belt".
%
% We may also consistently include the participation to an event that inhere the sum of the relata
% by adding  "|(?[E]:(event(E,W2) & paticipates(X,E,W2) & participates(Y,E,W2))))"





%%%%%%%%%%%Definition of Descriptive Relations:

fof(ax_def_descriptiverelations, axiom,
(![R] : (descriptiverelation(R) <=>
    (relation(R) & (?[W1,X,Y] : (world(W1) & iofr(X,Y,R,W1)) <=>
        (![W2,X,Y] : (iofr(X,Y,R,W2) <=>
            ((?[M,T]: (edm(M) & momenttype(T) & derive(R,T) & iof(M,T,W2) & ex(M,W2) & ((inheresIn(M,X) & ed(M,Y)) | (inheresIn(M,Y) & ed(M,X)))))
               | (?[P,Q,T]:(intrinsicmoment(P) & intrinsicmoment(Q) & momenttype(T) & derive(R,T) & iof(P,T,W2) & iof(Q,T,W2) & inheresIn(X,P) & ineheresIn(Y,Q)))
               | (?[M1,T1]:(momenttype(T1) & moment(M1) & (ineheresIn(M,S) <=> sum(Z,X,Y))
               )))))))))).



%%%%%%%%%%%Definition of non-descriptive Relations:

fof(ax_def_nondescriptiverelations, axiom, (![R]: (nondescriptiverelation(R) <=> (relation(R) & ~descriptiverelation(R))))).

%Test
%fof(ax_def_test, axiom, descriptiverelation(r)).
fof(ax_def_test, axiom, internalrelation(d) & ~descriptiverelation(d)).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Intrinsic moments, externally dependent modes
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5

fof(ax_moment, axiom, (![X]: (moment(X) <=> (endurant(X) & ?[Y]: inheresIn(X,Y))))).

%Externally dependent modes

fof(ax_edm, axiom, (![X]: (edm(X) <=> (mode(X) & ?[Y]: ((ed(X,Y) & (![Z]:(inheresIn(X,Z)) => ind(Z,Y)))))))).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relators
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%Proved consistent Darwin 1.4.4.

%%%%%%%%%%%Perdurants
fof(ax_def_perdurant, axiom, (![X] : perdurant(X) => individual(X))).
fof(ax_def_perdurant, axiom, (![X] : endurant(X) => individual(X))).
%fof(ax_def_perdurant_disjoint, axiom, (~?[X] : perdurant(X) & endurant(X))).
fof(ax_def_perdurant, axiom, (![X] : relator(X) => endurant(X))).
fof(ax_def_perdurant, axiom, (![X] : edm(X) => mode(X))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relators:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%founded by: externally depenent modes (edm) and relators are founded on perdurants.

fof(ax_def_founded_by, axiom, (![X,Y] : (foundedBy(X,Y) => (((edm(X) | relator(X))) & perdurant(Y))))).

%%%%%%Foundation is unique

fof(ax_def_founded_by_unique, axiom, (![X,Y,Z] : ((foundedBy(X,Y) & foundedBy(X,Z)) => Y=Z))).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%Relators: %A relator is the sum of the externally dependent modes inhering in one relatum, depending on the other, that share the same foundation.
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%A relator is the sum of the externally dependent modes inhering in one relatum, depending on the other, that share the same foundation.


        fof(ax_def_relator, axiom, (![X] : (relator(X) <=> ?[M,N,A,B,E]: (edm(M) & inheresIn(M,A) & edm(N) &inheresIn(N,B) & properPart(M,X) &
             properPart(N,X) & M != N & A!=B & ed(M,B) & ed(N,A))))).

        %Involves or mediates
        fof(ax_def_involves, axiom, (
            ![X,Y] : (involves(X,Y) <=>
                (relator(X) & endurant(Y) & (?[M]:(edm(M) & inheresIn(M,Y) & properPart(M,X))))))).



%Tests

      %fof(ax_def_test, axiom, mode(h)).
      %fof(ax_def_test, axiom, relator(g)).
      %fof(ax_def_test, axiom, foundedBy(g,p)).
      %fof(ax_def_test, axiom, involves(g,l)).



      /* ------------------------------------------------------------------------- */
      /* ------------------------------- CONJECTURES ----------------------------- */
      /* ------------------------------------------------------------------------- */

  %%% PROVEN CONJECTURE - descriptive/external relations, existence of truthmakers:

  fof(cj_descriptive_external, conjecture, (![R] : ((descriptiverelation(R) & externalrelation(R) & ?[W,X,Y]:(iofr(X,Y,R,W)))) =>
  (?[M,T]: (edm(M) & momenttype(T) & derive(R,T) & iof(M,T,W) & ((inheresIn(M,X) & ed(M,Y)) | (inheresIn(M,Y) & ed(Y,X))))))).

  %%%CONJECTURE

  %%% PROVEN CONJECTURE - Relators, existence of at least two externally dependent modes that are part of a relator:

  fof(cj_relators_at_least2edm, conjecture, (![R,X] : ((relator(R) & properPart(X,R)) => (?[M] :(properPart(M,R) & M != X))))).

  fof(cj_relators_at_least2edm2, conjecture, (![R,X] : ((relator(R) => (?[M,N] :(properPart(M,R) & properPart(N,R) & M != N)))))).


  %%% PROVEN CONJECTURE - Relators, existence of at least two different relata:

  fof(cj_relators_at_least2relata, conjecture, (![R] : ((relator(R) => (?[X,Y] :(involves(R,X) & involves(R,Y) & X != Y)))))).

  %%% PROVEN CONJECTURE - Relators, existence of at least two distinct relata:

  %fof(cj_relators_different_relata, conjecture, (![R,X] : ((relator(R) & properPart(M,R) & properPart(N,R) & M != N) => (?[Y,Z] :(involves(R,Y) & involves(R,Z) & Y != Z))))).
