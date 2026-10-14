-- Prove2me | solution 1 for GavrilSubtree.Chordal.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-12T02:10:59.513218+00:00
-- url     : https://prove2.me/submissions/465513d0-5c18-4a1b-a81e-716acbfe52c5

-- Complete checked reconstruction of the native Gavril subtree-intersection characterization.
-- Licensed under Apache 2.0.
import Definitions.Def_GavrilSubtree_Chordal_Setting
import Mathlib


-- Begin TreePathBasic

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {T : SimpleGraph V}

noncomputable def treePath (hT : T.IsTree) (x y : V) : T.Walk x y :=
  (hT.existsUnique_path x y).choose

theorem treePath_isPath (hT : T.IsTree) (x y : V) : (treePath hT x y).IsPath :=
  (hT.existsUnique_path x y).choose_spec.1

theorem treePath_unique (hT : T.IsTree) {x y : V} {p : T.Walk x y}
    (hp : p.IsPath) : p = treePath hT x y :=
  (hT.existsUnique_path x y).choose_spec.2 p hp

theorem treePath_length (hT : T.IsTree) (x y : V) :
    (treePath hT x y).length = T.dist x y := by
  obtain ⟨p, hp, hl⟩ := hT.connected.exists_path_of_dist x y
  simpa only [treePath_unique hT hp] using hl

theorem treePath_subset (hT : T.IsTree) {S : Set V}
    (hS : (T.induce S).Connected) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    ∀ z ∈ (treePath hT x y).support, z ∈ S := by
  let ι : (T.induce S) →g T := ⟨Subtype.val, fun h => h⟩
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨x,hx⟩ ⟨y,hy⟩
  have he : p.map ι = treePath hT x y := treePath_unique hT (hp.map Subtype.val_injective)
  intro z hz
  rw [← he, Walk.support_map] at hz
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
  exact a.property

theorem treePath_take [DecidableEq V] (hT : T.IsTree) {r x p : V}
    (hp : p ∈ (treePath hT r x).support) :
    (treePath hT r x).takeUntil p hp = treePath hT r p := by
  classical
  exact treePath_unique hT ((treePath_isPath hT r x).takeUntil hp)

theorem treePath_drop [DecidableEq V] (hT : T.IsTree) {r x p : V}
    (hp : p ∈ (treePath hT r x).support) :
    (treePath hT r x).dropUntil p hp = treePath hT p x := by
  classical
  exact treePath_unique hT ((treePath_isPath hT r x).dropUntil hp)

end GavrilSubtree.Chordal.Proof
-- End TreePathBasic

-- Begin LeafTree

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*}

def oldForest (T : SimpleGraph V) : SimpleGraph (Option V) where
  Adj a b := match a,b with
    | some x, some y => T.Adj x y
    | _, _ => False
  symm.symm := by intro a b h; cases a <;> cases b <;> simp_all [Adj.symm]
  loopless.irrefl := by intro a; cases a <;> simp

@[simp] theorem oldForest_some (T : SimpleGraph V) (x y : V) :
    (oldForest T).Adj (some x) (some y) ↔ T.Adj x y := Iff.rfl
@[simp] theorem oldForest_none (T : SimpleGraph V) (y : Option V) :
    ¬(oldForest T).Adj none y := by cases y <;> simp [oldForest]

def leafTree (T : SimpleGraph V) (p : V) : SimpleGraph (Option V) :=
  oldForest T ⊔ SimpleGraph.edge none (some p)

@[simp] theorem leafTree_some (T : SimpleGraph V) (p x y : V) :
    (leafTree T p).Adj (some x) (some y) ↔ T.Adj x y := by
  simp [leafTree, SimpleGraph.edge_adj]
@[simp] theorem leafTree_none (T : SimpleGraph V) (p : V) (y : Option V) :
    (leafTree T p).Adj none y ↔ y = some p := by
  cases y <;> simp [leafTree, SimpleGraph.edge_adj]

theorem oldForest_acyclic {T : SimpleGraph V} (hT : T.IsAcyclic) :
    (oldForest T).IsAcyclic := by
  classical
  let S : Set (Option V) := {x | x ≠ none}
  let f : (oldForest T).induce S →g T :=
    ⟨fun x => x.val.get (Option.isSome_iff_ne_none.mpr x.property), by
      intro a b h
      rcases a with ⟨a,ha⟩; rcases b with ⟨b,hb⟩
      cases a <;> cases b <;> simp_all [S, oldForest]⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have ha : some (f a) = a.val := Option.some_get _
    have hb : some (f b) = b.val := Option.some_get _
    exact ha.symm.trans ((congrArg some h).trans hb)
  have hac : ((oldForest T).induce S).IsAcyclic := hT.comap f hf
  intro u c hc
  have hs : ∀ x ∈ c.support, x ∈ S := by
    intro x hx he
    have hd := (hc.rotate hx).not_nil
    have ha := Walk.adj_snd hd
    subst x
    exact oldForest_none T _ ha
  have hc' : (c.induce S hs).IsCycle := by
    apply Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    simpa using hc
  exact hac _ hc'

theorem leafTree_isTree {T : SimpleGraph V} (hT : T.IsTree) (p : V) :
    (leafTree T p).IsTree := by
  have hn : ¬(oldForest T).Reachable none (some p) := by
    rintro ⟨q⟩
    cases q with
    | cons h q => exact oldForest_none T _ h
  have ha : (leafTree T p).IsAcyclic :=
    (oldForest_acyclic hT.isAcyclic).sup_edge_of_not_reachable hn
  refine ⟨?_,ha⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨some p,?_⟩
  intro x
  cases x with
  | none => exact (show (leafTree T p).Adj (some p) none from
      (leafTree_none T p (some p)).mpr rfl |>.symm).reachable
  | some x =>
    let f : T →g leafTree T p := ⟨some, fun h => (leafTree_some T p _ _).mpr h⟩
    exact (hT.connected p x).map f

end GavrilSubtree.Chordal.Proof
-- End LeafTree

-- Begin LeafSet

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*}

def leafSet (S : Set V) (b : Prop) : Set (Option V) :=
  {x | match x with | none => b | some y => y ∈ S}

@[simp] theorem leafSet_some (S : Set V) (b : Prop) (x : V) :
    some x ∈ leafSet S b ↔ x ∈ S := Iff.rfl
@[simp] theorem leafSet_none (S : Set V) (b : Prop) :
    none ∈ leafSet S b ↔ b := Iff.rfl

theorem leafSet_inter (S U : Set V) (b c : Prop) :
    (leafSet S b ∩ leafSet U c).Nonempty ↔ (S ∩ U).Nonempty ∨ b ∧ c := by
  constructor
  · rintro ⟨x,hx,hy⟩
    cases x with
    | none => exact Or.inr ⟨hx,hy⟩
    | some x => exact Or.inl ⟨x,hx,hy⟩
  · rintro (⟨x,hx,hy⟩ | ⟨hb,hc⟩)
    · exact ⟨some x,hx,hy⟩
    · exact ⟨none,hb,hc⟩

theorem leafSet_connected {T : SimpleGraph V} {S : Set V} (hS : (T.induce S).Connected)
    (p : V) (b : Prop) (hp : b → p ∈ S) :
    ((leafTree T p).induce (leafSet S b)).Connected := by
  let f : T.induce S →g (leafTree T p).induce (leafSet S b) :=
    ⟨fun x => ⟨some x.val,x.property⟩, fun h => (leafTree_some T p _ _).mpr h⟩
  obtain ⟨z⟩ := hS.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨f z,?_⟩
  rintro ⟨x,hx⟩
  cases x with
  | some x => exact (hS z ⟨x,hx⟩).map f
  | none =>
    have hps : p ∈ S := hp hx
    have hr := (hS z ⟨p,hps⟩).map f
    have ha : ((leafTree T p).induce (leafSet S b)).Adj (f ⟨p,hps⟩) ⟨none,hx⟩ :=
      ((leafTree_none T p (some p)).mpr rfl).symm
    exact hr.trans ha.reachable

theorem singleton_induce_connected (T : SimpleGraph V) (p : V) :
    (T.induce {p}).Connected := by
  exact (SimpleGraph.IsTree.of_subsingleton (G := T.induce {p})).connected

end GavrilSubtree.Chordal.Proof
-- End LeafSet

-- Begin TreeGate

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {T : SimpleGraph V}

theorem treePath_gate_step (hT : T.IsTree) {r p v w : V}
    (hp : p ∈ (treePath hT r v).support) (hvw : T.Adj v w)
    (hmin : T.dist r p ≤ T.dist r w) : p ∈ (treePath hT r w).support := by
  by_cases hv : v ∈ (treePath hT r w).support
  · have he := hT.isAcyclic.path_concat (treePath_isPath hT r v)
      (treePath_isPath hT r w) hvw hv
    rw [he]
    exact (treePath hT r v).support_subset_support_concat hvw hp
  · have hw := hT.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath
      (treePath_isPath hT r v) (treePath_isPath hT r w) hvw hv
    have he := hT.isAcyclic.path_concat (treePath_isPath hT r w)
      (treePath_isPath hT r v) hvw.symm hw
    have hlen := congrArg Walk.length he
    simp only [Walk.length_concat, treePath_length] at hlen
    have hpv : p ≠ v := by intro h; subst p; omega
    rw [he, Walk.support_concat, List.mem_append, List.mem_singleton] at hp
    exact hp.resolve_right hpv

theorem exists_tree_gate (hT : T.IsTree) (r : V) {S : Set V}
    (hS : (T.induce S).Connected) :
    ∃ p ∈ S, (∀ x ∈ S, T.dist r p ≤ T.dist r x) ∧
      ∀ x ∈ S, p ∈ (treePath hT r x).support := by
  classical
  obtain ⟨x⟩ := hS.nonempty
  have hex : ∃ n : ℕ, ∃ p ∈ S, T.dist r p = n := ⟨_, x, x.property, rfl⟩
  obtain ⟨p, hp, hpd⟩ := Nat.find_spec hex
  have hm : ∀ y ∈ S, T.dist r p ≤ T.dist r y := by
    intro y hy
    rw [hpd]
    exact Nat.find_min' hex ⟨y,hy,rfl⟩
  refine ⟨p,hp,hm,?_⟩
  have hw : ∀ {a b : S}, (T.induce S).Walk a b →
      p ∈ (treePath hT r a).support → p ∈ (treePath hT r b).support := by
    intro a b q
    induction q with
    | nil => exact id
    | @cons a b c hab q ih =>
      intro ha
      exact ih (treePath_gate_step hT ha hab (hm b b.property))
  intro y hy
  exact hw (hS ⟨p,hp⟩ ⟨y,hy⟩).some (treePath hT r p).end_mem_support

end GavrilSubtree.Chordal.Proof
-- End TreeGate

-- Begin TreeGateIntersection

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {T : SimpleGraph V}

theorem treePath_between_of_depth (hT : T.IsTree) {r x p q : V}
    (hp : p ∈ (treePath hT r x).support) (hq : q ∈ (treePath hT r x).support)
    (hle : T.dist r p ≤ T.dist r q) : q ∈ (treePath hT p x).support := by
  classical
  have he := (treePath hT r x).take_spec hp
  rw [treePath_take hT hp, treePath_drop hT hp] at he
  rw [← he, Walk.mem_support_append_iff] at hq
  rcases hq with hq | hq
  · by_cases hqp : q = p
    · subst q; exact (treePath hT p x).start_mem_support
    · have hh := (treePath hT r p).length_takeUntil_lt_length hq hqp
      rw [treePath_take hT hq, treePath_length, treePath_length] at hh
      omega
  · exact hq

theorem tree_gate_intersection (hT : T.IsTree) {r p q : V} {S U : Set V}
    (hS : (T.induce S).Connected) (hp : p ∈ S)
    (hpg : ∀ x ∈ S, p ∈ (treePath hT r x).support)
    (hqg : ∀ x ∈ U, q ∈ (treePath hT r x).support)
    (hle : T.dist r p ≤ T.dist r q) (hi : (S ∩ U).Nonempty) : q ∈ S := by
  obtain ⟨x,hx,hxu⟩ := hi
  exact treePath_subset hT hS hp hx q
    (treePath_between_of_depth hT (hpg x hx) (hqg x hxu) hle)

end GavrilSubtree.Chordal.Proof
-- End TreeGateIntersection

-- Begin TreeHelly

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V I : Type*} {T : SimpleGraph V} {F : I → Set V}

theorem deepest_subtree (hT : T.IsTree) (hF : ∀ i, (T.induce (F i)).Connected)
    (s : Finset I) (hs : s.Nonempty) :
    ∃ i ∈ s, ∃ p ∈ F i, ∀ j ∈ s, (F j ∩ F i).Nonempty → p ∈ F j := by
  classical
  obtain ⟨r⟩ := hT.connected.nonempty
  choose g hg hm hgate using fun i => exists_tree_gate hT r (hF i)
  obtain ⟨i, hi, hmax⟩ := s.exists_max_image (fun j => T.dist r (g j)) hs
  refine ⟨i,hi,g i,hg i,?_⟩
  intro j hj hji
  exact tree_gate_intersection hT (hF j) (hg j) (hgate j) (hgate i) (hmax j hj) hji

theorem finite_subtree_helly (hT : T.IsTree) (hF : ∀ i, (T.induce (F i)).Connected)
    (s : Finset I) (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (F i ∩ F j).Nonempty) :
    ∃ p, ∀ i ∈ s, p ∈ F i := by
  classical
  by_cases hs : s.Nonempty
  · obtain ⟨i,hi,p,hp,hdeep⟩ := deepest_subtree hT hF s hs
    refine ⟨p,fun j hj => ?_⟩
    by_cases hji : j = i
    · simpa only [hji] using hp
    · exact hdeep j hj (hpair j hj i hi hji)
  · obtain ⟨p⟩ := hT.connected.nonempty
    exact ⟨p,fun i hi => False.elim (hs ⟨i,hi⟩)⟩

end GavrilSubtree.Chordal.Proof
-- End TreeHelly

-- Begin LeafRepresentation

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
universe u
variable {V β : Type u} {G : SimpleGraph V} {v : V} {T : SimpleGraph β}
variable {F : {w : V // w ≠ v} → Set β}

noncomputable def extendSubtrees (G : SimpleGraph V) (v : V)
    (F : {w : V // w ≠ v} → Set β) (w : V) : Set (Option β) := by
  classical
  exact if h : w = v then {none} else leafSet (F ⟨w,h⟩) (G.Adj v w)

@[simp] theorem extendSubtrees_self : extendSubtrees G v F v = {none} := by
  classical
  simp [extendSubtrees]

theorem extendSubtrees_other {w : V} (hw : w ≠ v) :
    extendSubtrees G v F w = leafSet (F ⟨w,hw⟩) (G.Adj v w) := by
  classical
  simp [extendSubtrees, hw]

theorem extend_subtree_rep (h : IsSubtreeRep (G.induce {w | w ≠ v}) T F)
    (hv : IsSimplicial G v) (p : β)
    (hp : ∀ w : {w : V // w ≠ v}, G.Adj v w → p ∈ F w) :
    IsSubtreeRep G (leafTree T p) (extendSubtrees G v F) := by
  classical
  refine ⟨leafTree_isTree h.1 p,?_,?_⟩
  · intro w
    by_cases hw : w = v
    · subst w
      rw [extendSubtrees_self]
      exact singleton_induce_connected _ _
    · rw [extendSubtrees_other hw]
      exact leafSet_connected (h.2.1 ⟨w,hw⟩) p _ (hp ⟨w,hw⟩)
  · intro a b hab
    by_cases ha : a = v
    · subst a
      rw [extendSubtrees_self, extendSubtrees_other hab.symm]
      simp
    · by_cases hb : b = v
      · subst b
        rw [extendSubtrees_other ha, extendSubtrees_self]
        simp only [Set.inter_comm, Set.singleton_inter_nonempty, leafSet_none]
        exact ⟨Adj.symm, Adj.symm⟩
      · rw [extendSubtrees_other ha, extendSubtrees_other hb, leafSet_inter]
        have ho := h.2.2 ⟨a,ha⟩ ⟨b,hb⟩ (by intro he; exact hab (congrArg Subtype.val he))
        change G.Adj a b ↔ (F ⟨a,ha⟩ ∩ F ⟨b,hb⟩).Nonempty at ho
        constructor
        · exact fun hg => Or.inl (ho.mp hg)
        · rintro (hi | ⟨hva,hvb⟩)
          · exact ho.mpr hi
          · exact hv hva hvb hab

theorem extend_subtree_graph [Fintype V] (hv : IsSimplicial G v)
    (h : IsSubtreeGraph (G.induce {w | w ≠ v})) : IsSubtreeGraph G := by
  classical
  obtain ⟨β,T,F,h⟩ := h
  let s : Finset {w : V // w ≠ v} := Finset.univ.filter fun w => G.Adj v w
  obtain ⟨p,hp⟩ := finite_subtree_helly h.1 h.2.1 s (by
    intro a ha b hb hab
    apply (h.2.2 a b hab).mp
    exact hv (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      (by intro he; exact hab (Subtype.ext he)))
  exact ⟨Option β,leafTree T p,extendSubtrees G v F,
    extend_subtree_rep h hv p (fun w hw => hp w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩))⟩

end GavrilSubtree.Chordal.Proof
-- End LeafRepresentation

-- Begin RestrictedReach

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} (G : SimpleGraph V)

def restricted (U : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

@[simp] theorem restricted_adj (U : Set V) (x y : V) :
    (restricted G U).Adj x y ↔ G.Adj x y ∧ x ∈ U ∧ y ∈ U := Iff.rfl

theorem restricted_le (U : Set V) : restricted G U ≤ G := fun _ _ h => h.1

theorem reachable_closed {H : SimpleGraph V} {P : V → Prop} {a b : V}
    (h : H.Reachable a b) (ha : P a)
    (hc : ∀ x y, P x → H.Adj x y → P y) : P b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons h p ih => exact ih (hc _ _ ha h)

theorem restricted_reachable_mem {U : Set V} {a b : V}
    (h : (restricted G U).Reachable a b) (ha : a ∈ U) : b ∈ U :=
  reachable_closed h ha (fun _ _ _ hxy => hxy.2.2)

def region (U : Set V) (a : V) : Set V :=
  {x | x ∈ U ∧ (restricted G U).Reachable a x}

theorem region_self {U : Set V} {a : V} (ha : a ∈ U) : a ∈ region G U a :=
  ⟨ha, .rfl⟩

theorem region_step {U : Set V} {a x y : V} (hx : x ∈ region G U a)
    (hy : y ∈ U) (hxy : G.Adj x y) : y ∈ region G U a :=
  ⟨hy,hx.2.trans (Adj.reachable ⟨hxy,hx.1,hy⟩)⟩

theorem region_disjoint {U : Set V} {a b : V}
    (hab : ¬ (restricted G U).Reachable a b) :
    Disjoint (region G U a) (region G U b) := by
  rw [Set.disjoint_left]
  intro x hx hy
  exact hab (hx.2.trans hy.2.symm)

theorem region_no_cross {U : Set V} {a b x y : V}
    (hab : ¬ (restricted G U).Reachable a b)
    (hx : x ∈ region G U a) (hy : y ∈ region G U b) : ¬ G.Adj x y := by
  intro hxy
  exact hab ((hx.2.trans (Adj.reachable ⟨hxy,hx.1,hy.1⟩)).trans hy.2.symm)

theorem region_reachable {U : Set V} {a x y : V}
    (hx : x ∈ region G U a) (hy : y ∈ region G U a) :
    (restricted G (region G U a)).Reachable x y := by
  obtain ⟨p⟩ := hx.2.symm.trans hy.2
  suffices ∀ {x y} (p : (restricted G U).Walk x y), x ∈ region G U a →
      (restricted G (region G U a)).Reachable x y from this p hx
  intro x y p hxs
  induction p with
  | nil => exact .rfl
  | cons h p ih =>
    have hv := region_step G hxs h.2.2 h.1
    exact (Adj.reachable (G := restricted G (region G U a)) ⟨h.1,hxs,hv⟩).trans (ih hv)

end GavrilSubtree.Chordal.Proof
-- End RestrictedReach

-- Begin MinimalSeparator

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} (G : SimpleGraph V) (a b : V)

def Separates (S : Finset V) : Prop :=
  a ∉ S ∧ b ∉ S ∧ ¬ (restricted G ((S : Set V)ᶜ)).Reachable a b

theorem separates_symm {S : Finset V} (h : Separates G a b S) : Separates G b a S :=
  ⟨h.2.1,h.1,fun hr => h.2.2 hr.symm⟩

theorem exists_minimal_separator [Fintype V] (hab : a ≠ b) (hn : ¬G.Adj a b) :
    ∃ S, Minimal (Separates G a b) S := by
  classical
  apply exists_minimal_of_wellFoundedLT
  refine ⟨Finset.univ \ {a,b}, by simp, by simp, ?_⟩
  intro hr
  have heq : b = a := reachable_closed (P := fun x => x = a) hr rfl (fun x y hx hxy => by
    have hy : y = a ∨ y = b := by
      have hh := hxy.2.2
      simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ,
        Finset.mem_insert, Finset.mem_singleton, true_and, not_not] at hh
      exact hh
    rcases hy with rfl | rfl
    · rfl
    · exact (hn (hx ▸ hxy.1)).elim)
  exact hab heq.symm

theorem minimal_separator_neighbor {S : Finset V} (hS : Minimal (Separates G a b) S)
    {s : V} (hs : s ∈ S) :
    ∃ x ∈ region G ((S : Set V)ᶜ) a, G.Adj s x := by
  classical
  by_contra hn
  push Not at hn
  have herase : Separates G a b (S.erase s) := by
    refine ⟨fun h => hS.1.1 (Finset.mem_of_mem_erase h),
      fun h => hS.1.2.1 (Finset.mem_of_mem_erase h), ?_⟩
    intro hr
    have hb : b ∈ region G ((S : Set V)ᶜ) a := by
      apply reachable_closed hr (region_self G hS.1.1)
      intro x y hx hxy
      have hy : y ∉ S := by
        intro hys
        have hyne : y = s := by
          by_contra hne
          exact hxy.2.2 (Finset.mem_erase.mpr ⟨hne,hys⟩)
        subst y
        exact hn x hx hxy.1.symm
      exact region_step G hx hy hxy.1
    exact hS.1.2.2 hb.2
  have hh : S ⊆ S.erase s := hS.2 herase (Finset.erase_subset s S)
  have hh' := hh hs
  simp at hh'

theorem minimal_separator_symm {S : Finset V} (hS : Minimal (Separates G a b) S) :
    Minimal (Separates G b a) S := by
  refine ⟨separates_symm G a b hS.1, ?_⟩
  intro T hT hTS
  exact hS.2 (separates_symm G b a hT) hTS

end GavrilSubtree.Chordal.Proof
-- End MinimalSeparator

-- Begin ShortestChordless

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof

variable {V : Type*} {G : SimpleGraph V} {u v w : V}

theorem shortest_start_neighbor {p : G.Walk u v}
    (hp : p.length = G.dist u v) (hw : w ∈ p.support) (ha : G.Adj u w) :
    w = p.snd := by
  classical
  have hlen : (p.takeUntil w hw).length = 1 := by
    rw [length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hw)]
    exact dist_eq_one_iff_adj.mpr ha
  have h := p.getVert_length_takeUntil hw
  simpa [hlen] using h.symm

theorem shortest_chordless {p : G.Walk u v} (hp : p.length = G.dist u v) :
    p.IsChordless := by
  induction p with
  | nil => simp [Walk.isChordless_iff_forall_mem_edges]
  | @cons u v w h q ih =>
    have hq : q.length = G.dist v w :=
      length_eq_dist_of_subwalk hp (q.isSubwalk_cons h)
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    simp only [Walk.support_cons, List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · have he := shortest_start_neighbor hp (by simpa using hy) hxy
      subst y
      exact Walk.mk_start_snd_mem_edges (by simp)
    rcases hy with rfl | hy
    · have he := shortest_start_neighbor hp (by simp [hx]) hxy.symm
      subst x
      simpa only [Sym2.eq_swap] using
        (Walk.mk_start_snd_mem_edges (p := Walk.cons h q) (by simp))
    · exact List.mem_cons_of_mem _ ((ih hq).mem_edges hx hy hxy)

theorem exists_chordless_path (h : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.IsChordless := by
  obtain ⟨p, hp, hl⟩ := h.exists_path_of_dist
  exact ⟨p, hp, shortest_chordless hl⟩

end GavrilSubtree.Chordal.Proof
-- End ShortestChordless

-- Begin PathThroughSet

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem restricted_mono {A B : Set V} (h : A ⊆ B) : restricted G A ≤ restricted G B :=
  fun _ _ he => ⟨he.1,h he.2.1,h he.2.2⟩

theorem restricted_walk_support {A : Set V} {x y : V}
    (p : (restricted G A).Walk x y) (hx : x ∈ A) :
    ∀ z ∈ p.support, z ∈ A := by
  induction p with
  | nil => simpa using hx
  | cons h p ih =>
    intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih h.2.2 z hz

theorem exists_path_through_set {A : Set V} (hab : a ≠ b) (hn : ¬G.Adj a b)
    (hc : ∀ x ∈ A, ∀ y ∈ A, (restricted G A).Reachable x y)
    (ha : ∃ x ∈ A, G.Adj a x) (hb : ∃ y ∈ A, G.Adj b y) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.IsChordless ∧ 2 ≤ p.length ∧
      ∀ z ∈ p.support, z = a ∨ z = b ∨ z ∈ A := by
  classical
  let U := insert a (insert b A)
  have hAU : A ⊆ U := by intro x hx; simp [U,hx]
  obtain ⟨x,hx,hax⟩ := ha
  obtain ⟨y,hy,hby⟩ := hb
  have hr : (restricted G U).Reachable a b :=
    (Adj.reachable (G := restricted G U) ⟨hax,by simp [U],hAU hx⟩).trans
      (((hc x hx y hy).mono (restricted_mono hAU)).trans
        (Adj.reachable (G := restricted G U) ⟨hby.symm,hAU hy,by simp [U]⟩))
  obtain ⟨p,hp,hcp⟩ := exists_chordless_path hr
  let q := p.mapLe (restricted_le G U)
  have hs : ∀ z ∈ q.support, z ∈ U := by
    simpa [q] using restricted_walk_support p (by simp [U])
  refine ⟨q, hp.mapLe _, ?_, ?_, ?_⟩
  · rw [Walk.isChordless_iff_forall_mem_edges]
    intro z w hz hw hzw
    have hz' : z ∈ p.support := by simpa [q] using hz
    have hw' : w ∈ p.support := by simpa [q] using hw
    have he := hcp.mem_edges hz' hw' ⟨hzw,hs z hz,hs w hw⟩
    simpa [q] using he
  · have hdist := q.reachable.one_lt_dist_of_ne_of_not_adj hab hn
    have hle := dist_le q
    omega
  · intro z hz
    simpa [U] using hs z hz

end GavrilSubtree.Chordal.Proof
-- End PathThroughSet

-- Begin TwoPathCycle

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem path_start_not_tail {p : G.Walk a b} (hp : p.IsPath) : a ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← p.cons_tail_support, List.nodup_cons] at h
  exact h.1

theorem two_induced_paths_contradiction (hG : IsChordal G)
    {p q : G.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (hcp : p.IsChordless) (hcq : q.IsChordless)
    (hlp : 2 ≤ p.length) (hlq : 2 ≤ q.length)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hcross : ∀ x, x ∈ p.support → x ≠ a → x ≠ b →
      ∀ y, y ∈ q.support → y ≠ a → y ≠ b → ¬G.Adj x y) : False := by
  have hdis : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hz hz'
    have hzp := List.mem_of_mem_tail hz
    have hzq : z ∈ q.support := by simpa using List.mem_of_mem_tail hz'
    rcases hinter z hzp hzq with rfl | rfl
    · exact path_start_not_tail hp hz
    · exact path_start_not_tail hq.reverse hz'
  have hcy := hp.isCycle_append hq.reverse hdis (Or.inl (by omega))
  obtain ⟨x,hx,y,hy,hxy,he⟩ := hG a (p.append q.reverse) hcy (by simp; omega)
  have hs (z : V) : z ∈ (p.append q.reverse).support ↔ z ∈ p.support ∨ z ∈ q.support := by
    simp
  have hedgeP (hx : x ∈ p.support) (hy : y ∈ p.support) : False := by
    exact he (by simp [hcp.mem_edges hx hy hxy])
  have hedgeQ (hx : x ∈ q.support) (hy : y ∈ q.support) : False := by
    exact he (by simp [hcq.mem_edges hx hy hxy])
  rcases (hs x).mp hx with hx | hx <;> rcases (hs y).mp hy with hy | hy
  · exact hedgeP hx hy
  · have hxa : x ≠ a := fun h => hedgeQ (h ▸ q.start_mem_support) hy
    have hxb : x ≠ b := fun h => hedgeQ (h ▸ q.end_mem_support) hy
    have hya : y ≠ a := fun h => hedgeP hx (h ▸ p.start_mem_support)
    have hyb : y ≠ b := fun h => hedgeP hx (h ▸ p.end_mem_support)
    exact hcross x hx hxa hxb y hy hya hyb hxy
  · have hxa : x ≠ a := fun h => hedgeP (h ▸ p.start_mem_support) hy
    have hxb : x ≠ b := fun h => hedgeP (h ▸ p.end_mem_support) hy
    have hya : y ≠ a := fun h => hedgeQ hx (h ▸ q.start_mem_support)
    have hyb : y ≠ b := fun h => hedgeQ hx (h ▸ q.end_mem_support)
    exact hcross y hy hya hyb x hx hxa hxb hxy.symm
  · exact hedgeQ hx hy

end GavrilSubtree.Chordal.Proof
-- End TwoPathCycle

-- Begin SeparatorClique

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem minimal_separator_clique (hG : IsChordal G) {S : Finset V}
    (hS : Minimal (Separates G a b) S) : G.IsClique (S : Set V) := by
  intro x hx y hy hne
  by_contra hn
  let A := region G ((S : Set V)ᶜ) a
  let B := region G ((S : Set V)ᶜ) b
  have hca : ∀ z ∈ A, ∀ w ∈ A, (restricted G A).Reachable z w :=
    fun _ hz _ hw => region_reachable G hz hw
  have hcb : ∀ z ∈ B, ∀ w ∈ B, (restricted G B).Reachable z w :=
    fun _ hz _ hw => region_reachable G hz hw
  obtain ⟨p,hp,hcp,hlp,hps⟩ := exists_path_through_set hne hn hca
    (minimal_separator_neighbor G a b hS hx) (minimal_separator_neighbor G a b hS hy)
  have hS' := minimal_separator_symm G a b hS
  obtain ⟨q,hq,hcq,hlq,hqs⟩ := exists_path_through_set hne hn hcb
    (minimal_separator_neighbor G b a hS' hx) (minimal_separator_neighbor G b a hS' hy)
  have hdis : Disjoint A B := region_disjoint G hS.1.2.2
  apply two_induced_paths_contradiction hG hp hq hcp hcq hlp hlq
  · intro z hz hz'
    rcases hps z hz with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    rcases hqs z hz' with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
    · exact (Set.disjoint_left.mp hdis h h').elim
  · intro z hz hzx hzy w hw hwx hwy
    have hzA : z ∈ A := (hps z hz).resolve_left hzx |>.resolve_left hzy
    have hwB : w ∈ B := (hqs w hw).resolve_left hwx |>.resolve_left hwy
    exact region_no_cross G hS.1.2.2 hzA hwB

end GavrilSubtree.Chordal.Proof
-- End SeparatorClique

-- Begin ChordalTransport

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem chordal_of_embedding (f : H ↪g G) (hG : IsChordal G) : IsChordal H := by
  intro u c hc hl
  obtain ⟨x,hx,y,hy,hxy,he⟩ := hG (f u) (c.map f.toHom) (hc.map f.injective)
    (by simpa using hl)
  simp only [Walk.support_map, List.mem_map] at hx hy
  obtain ⟨x,hx,rfl⟩ := hx
  obtain ⟨y,hy,rfl⟩ := hy
  refine ⟨x,hx,y,hy,f.map_adj_iff.mp hxy,?_⟩
  intro h
  apply he
  rw [Walk.edges_map]
  exact List.mem_map.mpr ⟨s(x,y),h,rfl⟩

theorem chordal_induce (hG : IsChordal G) (U : Set V) : IsChordal (G.induce U) :=
  chordal_of_embedding (Embedding.induce U) hG

end GavrilSubtree.Chordal.Proof
-- End ChordalTransport

-- Begin SimplicialLocal

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {G : SimpleGraph V}

def DiracProperty (G : SimpleGraph V) : Prop :=
  G.IsClique Set.univ ∨ ∃ a b, a ≠ b ∧ ¬G.Adj a b ∧ IsSimplicial G a ∧ IsSimplicial G b

theorem simplicial_of_complete (h : G.IsClique Set.univ) (v : V) : IsSimplicial G v := by
  intro x _ y _ hxy
  exact h (Set.mem_univ x) (Set.mem_univ y) hxy

theorem local_simplicial_outside {S U : Set V} (hS : G.IsClique S)
    (hne : ∃ x ∈ U, x ∉ S) (hD : DiracProperty (G.induce U)) :
    ∃ x : U, x.1 ∉ S ∧ IsSimplicial (G.induce U) x := by
  rcases hD with hD | ⟨x,y,hxy,hn,hx,hy⟩
  · obtain ⟨x,hx,hxs⟩ := hne
    exact ⟨⟨x,hx⟩,hxs,simplicial_of_complete hD _⟩
  · by_cases hxs : x.1 ∈ S
    · have hys : y.1 ∉ S := by
        intro hys
        exact hn (hS hxs hys (fun he => hxy (Subtype.ext he)))
      exact ⟨y,hys,hy⟩
    · exact ⟨x,hxs,hx⟩

theorem simplicial_lift {U : Set V} {x : U}
    (hx : IsSimplicial (G.induce U) x)
    (hclosed : ∀ y, G.Adj x.1 y → y ∈ U) : IsSimplicial G x.1 := by
  intro y hy z hz hyz
  let y' : U := ⟨y,hclosed y hy⟩
  let z' : U := ⟨z,hclosed z hz⟩
  exact hx (x := y') (y := z') hy hz (fun h => hyz (congrArg Subtype.val h))

end GavrilSubtree.Chordal.Proof
-- End SimplicialLocal

-- Begin DiracInduction

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
universe u
variable {V : Type u} {G : SimpleGraph V}

theorem component_simplicial {a b : V} {S : Finset V}
    (hS : Separates G a b S) (hcl : G.IsClique (S : Set V))
    (hsmall : ∀ (U : Set V), (∃ z, z ∉ U) → DiracProperty (G.induce U)) :
    ∃ x ∈ region G ((S : Set V)ᶜ) a, IsSimplicial G x := by
  classical
  let A := region G ((S : Set V)ᶜ) a
  let U := (S : Set V) ∪ A
  have hb : b ∉ U := by
    rintro (hb | hb)
    · exact hS.2.1 hb
    · exact hS.2.2 hb.2
  have haA : a ∈ A := region_self G hS.1
  obtain ⟨x,hxs,hx⟩ := local_simplicial_outside hcl
    (U := U) ⟨a,Or.inr haA,hS.1⟩ (hsmall U ⟨b,hb⟩)
  have hxA : x.1 ∈ A := x.2.resolve_left hxs
  refine ⟨x.1,hxA,simplicial_lift hx ?_⟩
  intro y hxy
  by_cases hy : y ∈ S
  · exact Or.inl hy
  · exact Or.inr (region_step G hxA hy hxy)

private theorem dirac_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V = n →
      IsChordal G → DiracProperty G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G hcard hG
    by_cases hcomp : G.IsClique Set.univ
    · exact Or.inl hcomp
    obtain ⟨a,b,hab,hn⟩ := (G.not_isClique_iff).mp hcomp
    have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
    obtain ⟨S,hS⟩ := exists_minimal_separator G a.1 b.1 hab' hn
    have hcl := minimal_separator_clique hG hS
    have hsmall : ∀ (U : Set V), (∃ z, z ∉ U) → DiracProperty (G.induce U) := by
      intro U hU
      obtain ⟨z,hz⟩ := hU
      have hlt : Fintype.card U < n := hcard ▸ Fintype.card_subtype_lt hz
      exact ih (Fintype.card U) hlt U (G.induce U) rfl (chordal_induce hG U)
    obtain ⟨x,hx,hxs⟩ := component_simplicial hS.1 hcl hsmall
    obtain ⟨y,hy,hys⟩ := component_simplicial (separates_symm G a.1 b.1 hS.1) hcl hsmall
    have hne : x ≠ y := by
      intro he
      exact Set.disjoint_left.mp (region_disjoint G hS.1.2.2) hx (he ▸ hy)
    exact Or.inr ⟨x,y,hne,region_no_cross G hS.1.2.2 hx hy,hxs,hys⟩

theorem dirac_property [Fintype V] (hG : IsChordal G) : DiracProperty G :=
  dirac_card (Fintype.card V) V G rfl hG

theorem exists_simplicial [Fintype V] [Nonempty V] (hG : IsChordal G) : ∃ v, IsSimplicial G v := by
  rcases dirac_property hG with h | ⟨a,b,_,_,ha,_⟩
  · exact ⟨Classical.arbitrary V,simplicial_of_complete h _⟩
  · exact ⟨a,ha⟩

end GavrilSubtree.Chordal.Proof
-- End DiracInduction

-- Begin ChordalRepresentation

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
universe u

private theorem representation_card (n : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), Fintype.card V = n →
      IsChordal G → IsSubtreeGraph G := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V inst G hcard hG
    by_cases hn : Nonempty V
    · let : Nonempty V := hn
      obtain ⟨v,hv⟩ := exists_simplicial hG
      let S : Set V := {w | w ≠ v}
      have hlt : Fintype.card S < n := hcard ▸ Fintype.card_subtype_lt
        (show v ∉ S from by simp [S])
      exact extend_subtree_graph hv
        (ih (Fintype.card S) hlt S (G.induce S) rfl (chordal_induce hG S))
    · let : IsEmpty V := not_nonempty_iff.mp hn
      refine ⟨PUnit.{u+1}, ⊥, fun v => isEmptyElim v, ?_, ?_, ?_⟩
      · exact SimpleGraph.IsTree.of_subsingleton
      · exact fun v => isEmptyElim v
      · exact fun v => isEmptyElim v

theorem chordal_subtree_graph {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsChordal G) : IsSubtreeGraph G :=
  representation_card (Fintype.card V) V G rfl hG

end GavrilSubtree.Chordal.Proof
-- End ChordalRepresentation

-- Begin CycleChord

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
variable {V : Type*} {G : SimpleGraph V} {u v : V}

theorem cycle_neighbors_not_edge {c : G.Walk u u} (hc : c.IsCycle)
    (hl : 4 ≤ c.length) : s(c.snd, c.penultimate) ∉ c.edges := by
  intro he
  obtain ⟨i, hi, he⟩ := c.mk_mem_edges_iff_exists.mp he
  have hzero1 : c.getVert 0 ≠ c.getVert 1 := by
    intro h
    have hh := hc.getVert_injOn (x₁ := c.length) (x₂ := 1)
      (by simp; omega) (by simp; omega) (by simpa using h)
    omega
  have hzero2 : c.getVert 0 ≠ c.getVert (c.length - 1) := by
    intro h
    have hh := hc.getVert_injOn (x₁ := c.length) (x₂ := c.length - 1)
      (by simp; omega) (by simp; omega) (by simpa using h)
    omega
  rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · have hip : 1 ≤ i := by
      by_contra h
      have hi0 : i = 0 := by omega
      exact hzero1 (hi0 ▸ h1)
    have h1' := hc.getVert_injOn (by simp; omega) (by simp; omega) h1
    have h2' := hc.getVert_injOn (by simp; omega) (by simp; omega) h2
    omega
  · have hip : 1 ≤ i := by
      by_contra h
      have hi0 : i = 0 := by omega
      exact hzero2 (hi0 ▸ h1)
    have h1' := hc.getVert_injOn (by simp; omega) (by simp; omega) h1
    have h2' := hc.getVert_injOn (by simp; omega) (by simp; omega) h2
    omega

theorem cycle_chord_of_neighbor_clique {c : G.Walk u u} (hc : c.IsCycle)
    (hl : 4 ≤ c.length) (hv : v ∈ c.support)
    (hcl : G.IsClique {w | w ∈ c.support ∧ G.Adj v w}) :
    ∃ x ∈ c.support, ∃ y ∈ c.support, G.Adj x y ∧ s(x,y) ∉ c.edges := by
  classical
  let d := c.rotate v hv
  have hd : d.IsCycle := hc.rotate hv
  have hdl : 4 ≤ d.length := by simpa [d] using hl
  have hs : ∀ w, w ∈ d.support ↔ w ∈ c.support := fun w => c.mem_support_rotate_iff v hv
  have hx : d.snd ∈ c.support := (hs _).mp (d.getVert_mem_support 1)
  have hy : d.penultimate ∈ c.support := (hs _).mp (d.getVert_mem_support _)
  refine ⟨d.snd, hx, d.penultimate, hy, ?_, ?_⟩
  · exact hcl ⟨hx, Walk.adj_snd hd.not_nil⟩
      ⟨hy, (Walk.adj_penultimate hd.not_nil).symm⟩ hd.snd_ne_penultimate
  · intro he
    exact cycle_neighbors_not_edge hd hdl ((c.rotate_edges v hv).perm.mem_iff.mpr he)

end GavrilSubtree.Chordal.Proof
-- End CycleChord

-- Begin SubtreeChordal

open SimpleGraph
namespace GavrilSubtree.Chordal.Proof
universe u
variable {V β : Type u} {G : SimpleGraph V} {T : SimpleGraph β} {F : V → Set β}

theorem subtree_rep_chordal (h : IsSubtreeRep G T F) : IsChordal G := by
  classical
  intro u c hc hl
  obtain ⟨v,hv,p,hp,hd⟩ := deepest_subtree h.1 h.2.1 c.support.toFinset
    ⟨u,by simp⟩
  have hv' : v ∈ c.support := List.mem_toFinset.mp hv
  apply cycle_chord_of_neighbor_clique hc hl hv'
  intro a ha b hb hab
  apply (h.2.2 a b hab).mpr
  refine ⟨p,?_,?_⟩
  · exact hd a (List.mem_toFinset.mpr ha.1) ((h.2.2 a v ha.2.ne').mp ha.2.symm)
  · exact hd b (List.mem_toFinset.mpr hb.1) ((h.2.2 b v hb.2.ne').mp hb.2.symm)

theorem subtree_graph_chordal (h : IsSubtreeGraph G) : IsChordal G := by
  obtain ⟨β,T,F,h⟩ := h
  exact subtree_rep_chordal h

end GavrilSubtree.Chordal.Proof
-- End SubtreeChordal

-- Begin RootAssembly

namespace GavrilSubtree.Chordal
universe u

theorem theorem_3 {V : Type u} [Fintype V] (G : SimpleGraph V) :
    IsSubtreeGraph G ↔ IsChordal G :=
  ⟨Proof.subtree_graph_chordal, Proof.chordal_subtree_graph⟩

end GavrilSubtree.Chordal
-- End RootAssembly

-- Begin Solution

universe u

theorem solution {V : Type u} [Fintype V] (G : SimpleGraph V) :
    GavrilSubtree.Chordal.IsSubtreeGraph G ↔ GavrilSubtree.Chordal.IsChordal G :=
  GavrilSubtree.Chordal.theorem_3 G
-- End Solution
