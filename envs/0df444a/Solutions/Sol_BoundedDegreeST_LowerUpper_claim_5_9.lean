-- Prove2me | solution 1 for BoundedDegreeST.LowerUpper.claim_5_9
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T23:01:53.747411+00:00
-- url     : https://prove2.me/submissions/7f40425f-3494-43e7-a924-313eb0931b2e

import Definitions.Def_BoundedDegreeST_LowerUpper_Tokens



namespace BoundedDegreeST.LowerUpper

open Classical

set_option linter.unusedSectionVars false
set_option linter.deprecated false

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma mem_supernodeOf_iff (F : Finset (Sym2 V)) (v w : V) :
    w ∈ supernodeOf F v ↔ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Reachable v w := by
  simp [supernodeOf]

lemma self_mem_supernodeOf (F : Finset (Sym2 V)) (v : V) : v ∈ supernodeOf F v :=
  (mem_supernodeOf_iff F v v).2 (SimpleGraph.Reachable.refl _)

lemma supernodeOf_eq_of_mem (F : Finset (Sym2 V)) {v w : V} (h : w ∈ supernodeOf F v) :
    supernodeOf F w = supernodeOf F v := by
  rw [mem_supernodeOf_iff] at h
  ext u
  rw [mem_supernodeOf_iff, mem_supernodeOf_iff]
  exact ⟨fun hu => h.trans hu, fun hu => h.symm.trans hu⟩

lemma supernodeOf_disjoint_or_eq (F : Finset (Sym2 V)) (u v : V) :
    supernodeOf F u = supernodeOf F v ∨ Disjoint (supernodeOf F u) (supernodeOf F v) := by
  by_cases h : ∃ w, w ∈ supernodeOf F u ∧ w ∈ supernodeOf F v
  · obtain ⟨w, h1, h2⟩ := h
    left
    rw [← supernodeOf_eq_of_mem F h1, ← supernodeOf_eq_of_mem F h2]
  · right
    rw [Finset.disjoint_left]
    intro w h1 h2
    exact h ⟨w, h1, h2⟩

lemma mem_supernodes_iff (F : Finset (Sym2 V)) (C : Finset V) :
    C ∈ supernodes F ↔ ∃ v, supernodeOf F v = C := by
  simp [supernodes]

lemma compatible_supernodeOf (F : Finset (Sym2 V)) (v : V) :
    Compatible F (supernodeOf F v) := by
  intro C hC
  obtain ⟨u, rfl⟩ := (mem_supernodes_iff F C).1 hC
  rcases supernodeOf_disjoint_or_eq F u v with h | h
  · left; rw [h]
  · right; exact h

lemma compatible_union {F : Finset (Sym2 V)} {S T : Finset V}
    (hS : Compatible F S) (hT : Compatible F T) : Compatible F (S ∪ T) := by
  intro C hC
  rcases hS C hC with h1 | h1
  · left; exact h1.trans Finset.subset_union_left
  rcases hT C hC with h2 | h2
  · left; exact h2.trans Finset.subset_union_right
  · right; exact Finset.disjoint_union_right.2 ⟨h1, h2⟩

lemma compatible_compl {F : Finset (Sym2 V)} {S : Finset V}
    (hS : Compatible F S) : Compatible F Sᶜ := by
  intro C hC
  rcases hS C hC with h | h
  · right; exact Finset.disjoint_of_subset_left h disjoint_compl_right
  · left; intro w hw; rw [Finset.mem_compl]; exact Finset.disjoint_left.1 h hw

/-- F-edges do not cross compatible sets. -/
lemma mem_of_F_edge {F : Finset (Sym2 V)} {S : Finset V} (hS : Compatible F S)
    {a b : V} (he : s(a, b) ∈ F) (ha : a ∈ S) : b ∈ S := by
  by_cases hab : a = b
  · subst hab; exact ha
  have hadj : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Adj a b := by
    rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hab⟩
  have hb : b ∈ supernodeOf F a := (mem_supernodeOf_iff F a b).2 hadj.reachable
  rcases hS (supernodeOf F a) ((mem_supernodes_iff F _).2 ⟨a, rfl⟩) with h | h
  · exact h hb
  · exact absurd ha (Finset.disjoint_left.1 h (self_mem_supernodeOf F a))

lemma supernode_card_le (F : Finset (Sym2 V)) (v : V) :
    (supernodeOf F v).card ≤ (internal F (supernodeOf F v)).card + 1 := by
  have hconn := ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v).connected_toSimpleGraph
  have h1 := hconn.card_vert_le_card_edgeSet_add_one
  have hsupp : ∀ w, w ∈ ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v).supp
      ↔ w ∈ supernodeOf F v := by
    intro w
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, mem_supernodeOf_iff,
      SimpleGraph.ConnectedComponent.eq]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  have h2 : Nat.card ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v).supp
      = (supernodeOf F v).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hsupp)
  have h3 : Nat.card ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v).toSimpleGraph.edgeSet
      ≤ (internal F (supernodeOf F v)).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) ?_
    · obtain ⟨e, he⟩ := e
      induction e using Sym2.ind with
      | _ a b =>
        have he' : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Adj a.1 b.1 := he
        rw [SimpleGraph.fromEdgeSet_adj] at he'
        simp only [Sym2.map_pair_eq, internal, Finset.mem_filter, Sym2.mem_iff]
        refine ⟨he'.1, ?_⟩
        rintro w (rfl | rfl)
        · exact (hsupp _).1 a.2
        · exact (hsupp _).1 b.2
    · intro e1 e2 h
      apply Subtype.ext
      exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val h)
  have h4 : Nat.card ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v)
      = Nat.card ((SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).connectedComponentMk v).supp := rfl
  omega

lemma internal_univ (E : Finset (Sym2 V)) : internal E Finset.univ = E := by
  ext e; simp [internal]

lemma internal_subset (E : Finset (Sym2 V)) (S : Finset V) : internal E S ⊆ E := by
  intro e he; simp only [internal, Finset.mem_filter] at he; exact he.1

lemma cut_subset (E : Finset (Sym2 V)) (S : Finset V) : cut E S ⊆ E := by
  intro e he; simp only [cut, Finset.mem_filter] at he; exact he.1

lemma internal_mono (E : Finset (Sym2 V)) {S T : Finset V} (h : S ⊆ T) :
    internal E S ⊆ internal E T := by
  intro e he; simp only [internal, Finset.mem_filter] at he ⊢
  exact ⟨he.1, fun v hv => h (he.2 v hv)⟩

lemma edgeSum_split (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (S : Finset V) :
    PlusOne.edgeSum x (internal E Finset.univ) = PlusOne.edgeSum x (internal E S) +
      PlusOne.edgeSum x (internal E Sᶜ) + PlusOne.edgeSum x (cut E S) := by
  rw [internal_univ]
  unfold PlusOne.edgeSum internal cut
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _
  induction e using Sym2.ind with
  | _ a b =>
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

lemma edgeSum_one (X : Finset (Sym2 V)) : PlusOne.edgeSum (fun _ => (1 : ℝ)) X = X.card := by
  simp [PlusOne.edgeSum]

lemma cut_F_empty {F : Finset (Sym2 V)} {S : Finset V} (hS : Compatible F S) :
    cut F S = ∅ := by
  ext e
  simp only [cut, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
  intro he
  induction e using Sym2.ind with
  | _ a b =>
    rintro ⟨u, hu, huS⟩ ⟨w, hw, hwS⟩
    rw [Sym2.mem_iff] at hu hw
    have hab : a ∈ S → b ∈ S := fun h => mem_of_F_edge hS he h
    have hba : b ∈ S → a ∈ S := fun h => mem_of_F_edge hS (Sym2.eq_swap ▸ he) h
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> tauto

lemma card_split_F {F : Finset (Sym2 V)} {S : Finset V} (hS : Compatible F S) :
    ((internal F Finset.univ).card : ℝ) = (internal F S).card + (internal F Sᶜ).card := by
  have := edgeSum_split F (fun _ => (1 : ℝ)) S
  simp only [edgeSum_one, cut_F_empty hS, Finset.card_empty, Nat.cast_zero, add_zero] at this
  exact this

lemma card_compl_real (S : Finset V) :
    ((Fintype.card V : ℕ) : ℝ) = S.card + Sᶜ.card := by
  rw [← Finset.card_add_card_compl S]; push_cast; ring

lemma edgeSum_nonneg_of {E : Finset (Sym2 V)} {x : Sym2 V → ℝ} (hx : ∀ e ∈ E, 0 ≤ x e)
    {X : Finset (Sym2 V)} (hX : X ⊆ E) : 0 ≤ PlusOne.edgeSum x X :=
  Finset.sum_nonneg (fun e he => hx e (hX he))

lemma edgeSum_support (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (S : Finset V) :
    PlusOne.edgeSum x (cut E S) = PlusOne.edgeSum x (cut (support E x) S) := by
  unfold PlusOne.edgeSum
  have : cut (support E x) S = (cut E S).filter (fun e => x e ≠ 0) := by
    ext e; simp only [cut, support, Finset.mem_filter]; tauto
  rw [this, Finset.sum_filter_ne_zero]

section Feas

variable {E F : Finset (Sym2 V)} {A B : V → ℤ} {U W : Finset V} {x : Sym2 V → ℝ}

lemma supernode_tight (hfeas : Feasible E A B U W F x) (v : V) :
    PlusOne.edgeSum x (internal E (supernodeOf F v)) = 0 ∧
    ((internal F (supernodeOf F v)).card : ℝ) = (supernodeOf F v).card - 1 := by
  have h1 := hfeas.2.2.1 (supernodeOf F v) ⟨v, self_mem_supernodeOf F v⟩
    (compatible_supernodeOf F v)
  have h2 := edgeSum_nonneg_of hfeas.2.2.2.2.2 (internal_subset E (supernodeOf F v))
  have h3 : ((supernodeOf F v).card : ℝ) ≤ (internal F (supernodeOf F v)).card + 1 := by
    exact_mod_cast supernode_card_le F v
  constructor <;> linarith

lemma x_le_one (hE : PlusOne.SimpleEdges E) (hfeas : Feasible E A B U W F x)
    {e : Sym2 V} (he : e ∈ E) : x e ≤ 1 := by
  induction e using Sym2.ind with
  | _ a b =>
  set Q := supernodeOf F a ∪ supernodeOf F b with hQ
  have hQc : Compatible F Q := compatible_union (compatible_supernodeOf F a) (compatible_supernodeOf F b)
  have h1 := hfeas.2.2.1 Q ⟨a, Finset.mem_union_left _ (self_mem_supernodeOf F a)⟩ hQc
  have hint : s(a, b) ∈ internal E Q := by
    simp only [internal, Finset.mem_filter, Sym2.mem_iff]
    refine ⟨he, ?_⟩
    rintro w (rfl | rfl)
    · exact Finset.mem_union_left _ (self_mem_supernodeOf F _)
    · exact Finset.mem_union_right _ (self_mem_supernodeOf F _)
  have h2 : x s(a, b) ≤ PlusOne.edgeSum x (internal E Q) :=
    Finset.single_le_sum (fun e he => hfeas.2.2.2.2.2 e (internal_subset E Q he)) hint
  have ta := supernode_tight hfeas a
  have tb := supernode_tight hfeas b
  rcases supernodeOf_disjoint_or_eq F a b with h | h
  · have : Q = supernodeOf F a := by rw [hQ, h, Finset.union_self]
    rw [this] at h1 h2
    linarith
  · have hcard : (Q.card : ℝ) = (supernodeOf F a).card + (supernodeOf F b).card := by
      rw [hQ, Finset.card_union_of_disjoint h]; push_cast; ring
    have hdisj : Disjoint (internal F (supernodeOf F a)) (internal F (supernodeOf F b)) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      simp only [internal, Finset.mem_filter] at h1 h2
      have hw := Sym2.out_fst_mem e
      exact Finset.disjoint_left.1 h (h1.2 _ hw) (h2.2 _ hw)
    have hsub : internal F (supernodeOf F a) ∪ internal F (supernodeOf F b) ⊆ internal F Q :=
      Finset.union_subset (internal_mono F Finset.subset_union_left)
        (internal_mono F Finset.subset_union_right)
    have hF : ((internal F (supernodeOf F a)).card : ℝ) + (internal F (supernodeOf F b)).card
        ≤ (internal F Q).card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hdisj] at this
      exact_mod_cast this
    linarith

/-- A tight compatible proper nonempty set has cut value at least one. -/
lemma cut_ge_one (hfeas : Feasible E A B U W F x) {S : Finset V}
    (hSc : Compatible F S) (hSV : S ≠ Finset.univ)
    (htight : PlusOne.edgeSum x (internal E S) = (S.card : ℝ) - ((internal F S).card : ℝ) - 1) :
    1 ≤ PlusOne.edgeSum x (cut E S) := by
  have hne : (Sᶜ).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h
    exact hSV (by rw [← compl_compl S, h, Finset.compl_empty])
  have h1 := hfeas.2.2.1 Sᶜ hne (compatible_compl hSc)
  have h2 := hfeas.2.1
  have h3 := edgeSum_split E x S
  have h4 := card_split_F (F := F) hSc
  have h5 := card_compl_real S
  linarith

end Feas

theorem claim_5_7_core
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ) :
    2 ≤ (cut (support E x) S).card := by
  have hfeas := hbasic.1
  have h1 := cut_ge_one hfeas (hbasis.2.2.1 S hS).2 hSV (hbasis.2.2.2.2.2.2.2.1 S hS)
  rw [edgeSum_support] at h1
  by_contra hlt
  push_neg at hlt
  rcases Nat.lt_or_ge (cut (support E x) S).card 1 with h0 | h0
  · have : cut (support E x) S = ∅ := Finset.card_eq_zero.1 (by omega)
    rw [this] at h1
    simp [PlusOne.edgeSum] at h1
    linarith
  · obtain ⟨e, he⟩ := Finset.card_eq_one.1 (by omega : (cut (support E x) S).card = 1)
    have hmem : e ∈ cut (support E x) S := by rw [he]; exact Finset.mem_singleton_self e
    rw [he] at h1
    simp only [PlusOne.edgeSum, Finset.sum_singleton] at h1
    have hsup : e ∈ support E x := cut_subset _ _ hmem
    have hEe : e ∈ E := by
      simp only [support, Finset.mem_filter] at hsup; exact hsup.1
    have := x_le_one hE hfeas hEe
    exact hnoone e hsup (le_antisymm this h1)

lemma degree_eq_card_of (X : Finset (Sym2 V)) (w : V) (D : Finset (Sym2 V))
    (hD : ∀ e, e ∈ D ↔ e ∈ X ∧ w ∈ e) : degree X w = D.card := by
  obtain ⟨D', hD', h⟩ : ∃ D' : Finset (Sym2 V), (∀ e, e ∈ D' ↔ e ∈ X ∧ w ∈ e) ∧
      degree X w = D'.card := by
    refine ⟨_, ?_, rfl⟩; intro e; simp only [Finset.mem_filter]
  rw [h]; congr 1; ext e; rw [hD, hD']

lemma supernodeExcess_eq (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (T C P : Finset V)
    (hP : ∀ w, w ∈ P ↔ w ∈ C ∧ Active E x w) :
    supernodeExcess E x T C = ∑ w ∈ P, vertexExcess E x T w := by
  obtain ⟨P', hP', h⟩ : ∃ P' : Finset V, (∀ w, w ∈ P' ↔ w ∈ C ∧ Active E x w) ∧
      supernodeExcess E x T C = ∑ w ∈ P', vertexExcess E x T w := by
    refine ⟨_, ?_, rfl⟩; intro w; simp only [Finset.mem_filter]
  rw [h]; congr 1; ext w; rw [hP, hP']

lemma active_of_mem (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) {e : Sym2 V} {u : V}
    (he : e ∈ support E x) (hu : u ∈ e) : Active E x u := by
  unfold Active
  rw [degree_eq_card_of (support E x) u ((support E x).filter (fun f => u ∈ f))
    (fun f => Finset.mem_filter)]
  exact Finset.card_pos.2 ⟨e, Finset.mem_filter.2 ⟨he, hu⟩⟩

lemma cut_single_support (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (hE : PlusOne.SimpleEdges E)
    (w : V) : cut (support E x) {w} = (support E x).filter (fun f => w ∈ f) := by
  ext f
  simp only [cut, support, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, ⟨v, hv, rfl⟩, _⟩; exact ⟨h1, hv⟩
  · rintro ⟨h1, hw⟩
    refine ⟨h1, ⟨w, hw, rfl⟩, ?_⟩
    have hnd := hE f h1.1
    induction f using Sym2.ind with
    | _ a b =>
      rw [Sym2.mk_isDiag_iff] at hnd
      rw [Sym2.mem_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨b, Sym2.mem_mk_right _ _, fun h => hnd h.symm⟩
      · exact ⟨a, Sym2.mem_mk_left _ _, hnd⟩

lemma not_deg_one_of_tight {E F : Finset (Sym2 V)} {A B : V → ℤ} {U W : Finset V}
    {x : Sym2 V → ℝ} (hE : PlusOne.SimpleEdges E) (hfeas : Feasible E A B U W F x)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1) (w : V) (k : ℤ)
    (htight : PlusOne.edgeSum x (cut E {w}) = (k : ℝ))
    (hdeg : degree (support E x) w = 1) : False := by
  rw [degree_eq_card_of (support E x) w ((support E x).filter (fun f => w ∈ f))
    (fun f => Finset.mem_filter)] at hdeg
  obtain ⟨e, he⟩ := Finset.card_eq_one.1 hdeg
  rw [edgeSum_support, cut_single_support E x hE, he] at htight
  simp only [PlusOne.edgeSum, Finset.sum_singleton] at htight
  have hmem : e ∈ (support E x).filter (fun f => w ∈ f) := by
    rw [he]; exact Finset.mem_singleton_self e
  have hsup : e ∈ support E x := (Finset.mem_filter.1 hmem).1
  have hEe : e ∈ E := by simp only [support, Finset.mem_filter] at hsup; exact hsup.1
  have hne : x e ≠ 0 := by simp only [support, Finset.mem_filter] at hsup; exact hsup.2
  have h0 := hfeas.2.2.2.2.2 e hEe
  have h1 := x_le_one hE hfeas hEe
  have h1' := hnoone e hsup
  have hpos : 0 < (k : ℝ) := by rw [← htight]; exact lt_of_le_of_ne h0 (Ne.symm hne)
  have hlt : (k : ℝ) < 1 := by rw [← htight]; exact lt_of_le_of_ne h1 h1'
  have : (0 : ℤ) < k := by exact_mod_cast hpos
  have : k < (1 : ℤ) := by exact_mod_cast hlt
  omega

theorem claim_5_4_core
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E)
    (hbasic : Basic E A B U W F x)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (C : Finset V) (hC : IsSpecialSupernode E F x (TU ∪ TW) C) :
    ∃ v ∈ C, Active E x v ∧ (∀ w ∈ C, Active E x w → w = v) ∧
      v ∈ TU ∪ TW ∧ degree (support E x) v = 3 := by
  have hfeas := hbasic.1
  obtain ⟨hCmem, hexc⟩ := hC
  obtain ⟨v0, rfl⟩ := (mem_supernodes_iff F C).1 hCmem
  have tight := supernode_tight hfeas v0
  have hZ : ∀ e ∈ internal E (supernodeOf F v0), x e = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e he => hfeas.2.2.2.2.2 e (internal_subset E _ he))).1 tight.1
    exact this
  have hTUW : ∀ w ∈ TU ∪ TW, w ∈ U ∪ W := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · exact Finset.mem_union_left _ (hbasis.2.2.2.1 h)
    · exact Finset.mem_union_right _ (hbasis.2.2.2.2.1 h)
  have hdeg1 : ∀ w ∈ TU ∪ TW, degree (support E x) w ≠ 1 := by
    intro w hw hd
    rcases Finset.mem_union.1 hw with h | h
    · exact not_deg_one_of_tight hE hfeas hnoone w (A w) (hbasis.2.2.2.2.2.1 w h) hd
    · exact not_deg_one_of_tight hE hfeas hnoone w (B w) (hbasis.2.2.2.2.2.2.1 w h) hd
  have hge : ∀ w, Active E x w → 1 ≤ vertexExcess E x (TU ∪ TW) w := by
    intro w hw
    unfold Active at hw
    unfold vertexExcess
    by_cases hT : w ∈ TU ∪ TW
    · rw [if_pos hT]
      have h2 := hnodeg2 w (hTUW w hT)
      have h1 := hdeg1 w hT
      have : 3 ≤ degree (support E x) w := by omega
      omega
    · rw [if_neg hT]; omega
  set P := (supernodeOf F v0).filter (fun w => Active E x w) with hPdef
  have hP : ∀ w, w ∈ P ↔ w ∈ supernodeOf F v0 ∧ Active E x w := fun w => Finset.mem_filter
  rw [supernodeExcess_eq E x _ _ P hP] at hexc
  have hcard : (P.card : ℤ) ≤ 1 := by
    have : ∑ w ∈ P, (1 : ℤ) ≤ ∑ w ∈ P, vertexExcess E x (TU ∪ TW) w :=
      Finset.sum_le_sum (fun w hw => hge w ((hP w).1 hw).2)
    simp at this; omega
  have hPne : P.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro h; rw [h] at hexc; simp at hexc
  have hP1 : P.card = 1 := by
    have := Finset.card_pos.2 hPne; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 hP1
  have hvP : v ∈ P := by rw [hv]; exact Finset.mem_singleton_self v
  rw [hv, Finset.sum_singleton] at hexc
  have huniq : ∀ w ∈ supernodeOf F v0, Active E x w → w = v := by
    intro w hw ha
    have : w ∈ P := (hP w).2 ⟨hw, ha⟩
    rw [hv] at this; exact Finset.mem_singleton.1 this
  refine ⟨v, ((hP v).1 hvP).1, ((hP v).1 hvP).2, huniq, ?_⟩
  unfold vertexExcess at hexc
  by_cases hT : v ∈ TU ∪ TW
  · rw [if_pos hT] at hexc
    exact ⟨hT, by omega⟩
  · exfalso
    rw [if_neg hT] at hexc
    have hdeg : degree (support E x) v = 1 := by omega
    rw [degree_eq_card_of (support E x) v ((support E x).filter (fun f => v ∈ f))
      (fun f => Finset.mem_filter)] at hdeg
    obtain ⟨e, he⟩ := Finset.card_eq_one.1 hdeg
    have hmem : e ∈ (support E x).filter (fun f => v ∈ f) := by
      rw [he]; exact Finset.mem_singleton_self e
    have hsup : e ∈ support E x := (Finset.mem_filter.1 hmem).1
    have hEe : e ∈ E := by simp only [support, Finset.mem_filter] at hsup; exact hsup.1
    have hne : x e ≠ 0 := by simp only [support, Finset.mem_filter] at hsup; exact hsup.2
    have hCV : supernodeOf F v0 ≠ Finset.univ := by
      intro hU
      apply hne
      apply hZ
      rw [hU, internal_univ]; exact hEe
    have h1 := cut_ge_one hfeas (compatible_supernodeOf F v0) hCV (by rw [tight.1, tight.2]; ring)
    rw [edgeSum_support] at h1
    have hsub : cut (support E x) (supernodeOf F v0) ⊆ {e} := by
      intro f hf
      have hfs : f ∈ support E x := cut_subset _ _ hf
      simp only [cut, Finset.mem_filter] at hf
      obtain ⟨_, ⟨u, hu, huC⟩, _⟩ := hf
      have hua := active_of_mem E x hfs hu
      have := huniq u huC hua
      subst this
      rw [← he]; exact Finset.mem_filter.2 ⟨hfs, hu⟩
    have h2 : PlusOne.edgeSum x (cut (support E x) (supernodeOf F v0)) ≤ PlusOne.edgeSum x {e} :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f hf _ => by
        rw [Finset.mem_singleton.1 hf]; exact hfeas.2.2.2.2.2 e hEe)
    simp only [PlusOne.edgeSum, Finset.sum_singleton] at h2
    have h3 := x_le_one hE hfeas hEe
    exact hnoone e hsup (le_antisymm h3 (by unfold PlusOne.edgeSum at h1; linarith))

section Members

variable {F : Finset (Sym2 V)} {L : Finset (Finset V)}

lemma mem_members_iff (S R : Finset V) :
    R ∈ members F L S ↔ IsChild L S R ∨
      (R ∈ supernodes F ∧ R ⊆ S ∧ ∀ R' ∈ children L S, ¬ R ⊆ R') := by
  unfold members children
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨_, h⟩ | h)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h.1, h⟩
    · exact Or.inr h

lemma mem_children_iff (S R : Finset V) : R ∈ children L S ↔ IsChild L S R := by
  unfold children; simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma children_disjoint (hL : PlusOne.Laminar L) {S R1 R2 : Finset V}
    (h1 : IsChild L S R1) (h2 : IsChild L S R2) (hne : R1 ≠ R2) : Disjoint R1 R2 := by
  by_contra hnd
  rw [Finset.not_disjoint_iff_nonempty_inter] at hnd
  have hlam := hL R1 h1.1 R2 h2.1
  unfold PlusOne.Intersecting at hlam
  have : ¬ (R1 \ R2).Nonempty ∨ ¬ (R2 \ R1).Nonempty := by tauto
  rcases this with h | h
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact h1.2.2 R2 h2.1 (Finset.ssubset_iff_subset_ne.2 ⟨h, hne⟩) h2.2.1
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact h2.2.2 R1 h1.1 (Finset.ssubset_iff_subset_ne.2 ⟨h, Ne.symm hne⟩) h1.2.1

lemma child_supernode_disjoint (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S) {S R C : Finset V}
    (h1 : IsChild L S R) (h2 : C ∈ supernodes F ∧ C ⊆ S ∧ ∀ R' ∈ children L S, ¬ C ⊆ R') :
    Disjoint R C := by
  rcases (hLc R h1.1).2 C h2.1 with h | h
  · exact absurd h (h2.2.2 R ((mem_children_iff S R).2 h1))
  · exact h.symm

lemma members_disjoint (hL : PlusOne.Laminar L) (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S)
    {S R1 R2 : Finset V} (h1 : R1 ∈ members F L S) (h2 : R2 ∈ members F L S) (hne : R1 ≠ R2) :
    Disjoint R1 R2 := by
  rw [mem_members_iff] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact children_disjoint hL h1 h2 hne
  · exact child_supernode_disjoint hLc h1 h2
  · exact (child_supernode_disjoint hLc h2 h1).symm
  · obtain ⟨u, rfl⟩ := (mem_supernodes_iff F _).1 h1.1
    obtain ⟨v, rfl⟩ := (mem_supernodes_iff F _).1 h2.1
    rcases supernodeOf_disjoint_or_eq F u v with h | h
    · exact absurd h hne
    · exact h

lemma members_subset {S R : Finset V} (h : R ∈ members F L S) : R ⊆ S := by
  rw [mem_members_iff] at h
  rcases h with h | h
  · exact h.2.1.1
  · exact h.2.1

lemma members_cover (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S) {S : Finset V} (hS : S ∈ L)
    {v : V} (hv : v ∈ S) : ∃ R ∈ members F L S, v ∈ R := by
  by_cases h : ∃ R ∈ children L S, v ∈ R
  · obtain ⟨R, hR, hvR⟩ := h
    exact ⟨R, (mem_members_iff S R).2 (Or.inl ((mem_children_iff S R).1 hR)), hvR⟩
  · push_neg at h
    refine ⟨supernodeOf F v, (mem_members_iff S _).2 (Or.inr ⟨(mem_supernodes_iff F _).2 ⟨v, rfl⟩,
      ?_, ?_⟩), self_mem_supernodeOf F v⟩
    · rcases (hLc S hS).2 (supernodeOf F v) ((mem_supernodes_iff F _).2 ⟨v, rfl⟩) with h' | h'
      · exact h'
      · exact absurd hv (Finset.disjoint_left.1 h' (self_mem_supernodeOf F v))
    · intro R hR hsub
      exact h R hR (hsub (self_mem_supernodeOf F v))

lemma members_unique (hL : PlusOne.Laminar L) (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S)
    {S R1 R2 : Finset V} (h1 : R1 ∈ members F L S) (h2 : R2 ∈ members F L S) {v : V}
    (hv1 : v ∈ R1) (hv2 : v ∈ R2) : R1 = R2 := by
  by_contra hne
  exact Finset.disjoint_left.1 (members_disjoint hL hLc h1 h2 hne) hv1 hv2

end Members

theorem claim_5_8_core (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hfeas : Feasible E A B U W F x)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (S : Finset V) (hS : S ∈ L) :
    BoundedDegreeST.PlusOne.edgeSum x (crossing E F x L S) = ((members F L S).card : ℝ) - 1 := by
  have hL := hbasis.2.1
  have hLc := hbasis.2.2.1
  have htightL := hbasis.2.2.2.2.2.2.2.1
  set M := members F L S with hM
  -- member facts
  have hmem : ∀ R ∈ M, Compatible F R ∧
      PlusOne.edgeSum x (internal E R) = (R.card : ℝ) - ((internal F R).card : ℝ) - 1 := by
    intro R hR
    rw [hM, mem_members_iff] at hR
    rcases hR with h | h
    · exact ⟨(hLc R h.1).2, htightL R h.1⟩
    · obtain ⟨u, rfl⟩ := (mem_supernodes_iff F _).1 h.1
      have t := supernode_tight hfeas u
      exact ⟨compatible_supernodeOf F u, by rw [t.1, t.2]; ring⟩
  have hdisj : ∀ R1 ∈ M, ∀ R2 ∈ M, R1 ≠ R2 → Disjoint R1 R2 :=
    fun R1 h1 R2 h2 hne => members_disjoint hL hLc h1 h2 hne
  -- (c1)
  have hS_eq : S = M.biUnion id := by
    ext v
    simp only [Finset.mem_biUnion, id]
    constructor
    · intro hv; exact members_cover hLc hS hv
    · rintro ⟨R, hR, hvR⟩; exact members_subset hR hvR
  have hc1 : (S.card : ℝ) = ∑ R ∈ M, (R.card : ℝ) := by
    have : S.card = ∑ R ∈ M, R.card := by
      conv_lhs => rw [hS_eq]
      rw [Finset.card_biUnion]
      · rfl
      · intro R1 h1 R2 h2 hne; exact hdisj R1 h1 R2 h2 hne
    rw [this]; push_cast; rfl
  -- (c2)
  have hFS_eq : internal F S = M.biUnion (fun R => internal F R) := by
    ext e
    simp only [Finset.mem_biUnion]
    constructor
    · intro he
      have he' := he
      simp only [internal, Finset.mem_filter] at he'
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨R, hR, haR⟩ := members_cover hLc hS (he'.2 a (Sym2.mem_mk_left a b))
        have hbR : b ∈ R := mem_of_F_edge (hmem R hR).1 he'.1 haR
        refine ⟨R, hR, ?_⟩
        simp only [internal, Finset.mem_filter, Sym2.mem_iff]
        refine ⟨he'.1, ?_⟩
        rintro w (rfl | rfl)
        · exact haR
        · exact hbR
    · rintro ⟨R, hR, he⟩
      exact internal_mono F (members_subset hR) he
  have hc2 : ((internal F S).card : ℝ) = ∑ R ∈ M, ((internal F R).card : ℝ) := by
    have : (internal F S).card = ∑ R ∈ M, (internal F R).card := by
      rw [hFS_eq, Finset.card_biUnion]
      intro R1 h1 R2 h2 hne
      show Disjoint (internal F R1) (internal F R2)
      rw [Finset.disjoint_left]
      intro e he1 he2
      simp only [internal, Finset.mem_filter] at he1 he2
      have hw := Sym2.out_fst_mem e
      exact Finset.disjoint_left.1 (hdisj R1 h1 R2 h2 hne) (he1.2 _ hw) (he2.2 _ hw)
    rw [this]; push_cast; rfl
  -- (c3)
  have hDsub : crossing E F x L S ⊆ internal E S := by
    intro e he
    unfold crossing at he
    rw [Finset.mem_filter] at he
    obtain ⟨hsup, R1, h1, R2, h2, _, u, hu, w, hw, rfl⟩ := he
    simp only [support, Finset.mem_filter] at hsup
    simp only [internal, Finset.mem_filter, Sym2.mem_iff]
    refine ⟨hsup.1, ?_⟩
    rintro v (rfl | rfl)
    · exact members_subset h1 hu
    · exact members_subset h2 hw
  have hpt : ∀ e ∈ internal E S, x e = (if e ∈ crossing E F x L S then x e else 0) +
      ∑ R ∈ M, (if e ∈ internal E R then x e else 0) := by
    intro e he
    by_cases hx : x e = 0
    · simp [hx]
    have he' := he
    simp only [internal, Finset.mem_filter] at he'
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨Ra, hRa, haR⟩ := members_cover hLc hS (he'.2 a (Sym2.mem_mk_left a b))
      obtain ⟨Rb, hRb, hbR⟩ := members_cover hLc hS (he'.2 b (Sym2.mem_mk_right a b))
      by_cases hab : Ra = Rb
      · subst hab
        have hnotD : s(a, b) ∉ crossing E F x L S := by
          intro hD
          unfold crossing at hD
          rw [Finset.mem_filter] at hD
          obtain ⟨_, R1, h1, R2, h2, hne, u, hu, w, hw, heq⟩ := hD
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hne ((members_unique hL hLc h1 hRa hu haR).trans
              (members_unique hL hLc hRa h2 hbR hw))
          · exact hne ((members_unique hL hLc h1 hRa hu hbR).trans
              (members_unique hL hLc hRa h2 haR hw))
        rw [if_neg hnotD, zero_add]
        rw [Finset.sum_eq_single Ra]
        · rw [if_pos]
          simp only [internal, Finset.mem_filter, Sym2.mem_iff]
          refine ⟨he'.1, ?_⟩
          rintro w (rfl | rfl)
          · exact haR
          · exact hbR
        · intro R hR hne
          rw [if_neg]
          intro hin
          simp only [internal, Finset.mem_filter] at hin
          exact hne (members_unique hL hLc hR hRa (hin.2 a (Sym2.mem_mk_left a b)) haR)
        · intro h; exact absurd hRa h
      · have hD : s(a, b) ∈ crossing E F x L S := by
          unfold crossing
          rw [Finset.mem_filter]
          refine ⟨?_, Ra, hRa, Rb, hRb, hab, a, haR, b, hbR, rfl⟩
          simp only [support, Finset.mem_filter]; exact ⟨he'.1, hx⟩
        rw [if_pos hD, Finset.sum_eq_zero, add_zero]
        intro R hR
        rw [if_neg]
        intro hin
        simp only [internal, Finset.mem_filter] at hin
        exact hab ((members_unique hL hLc hRa hR haR (hin.2 a (Sym2.mem_mk_left a b))).trans
          (members_unique hL hLc hR hRb (hin.2 b (Sym2.mem_mk_right a b)) hbR))
  have hc3 : PlusOne.edgeSum x (internal E S) = PlusOne.edgeSum x (crossing E F x L S) +
      ∑ R ∈ M, PlusOne.edgeSum x (internal E R) := by
    unfold PlusOne.edgeSum
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_comm]
    congr 1
    · rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hDsub]
    · refine Finset.sum_congr rfl ?_
      intro R hR
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 (internal_mono E (members_subset hR))]
  have hsumR : ∑ R ∈ M, PlusOne.edgeSum x (internal E R) =
      ∑ R ∈ M, ((R.card : ℝ) - ((internal F R).card : ℝ) - 1) :=
    Finset.sum_congr rfl (fun R hR => (hmem R hR).2)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← hc1, ← hc2] at hsumR
  have htS := htightL S hS
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsumR
  linarith

lemma ind_val (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (X : Finset (Sym2 V))
    (e : {e : Sym2 V // e ∈ support E x}) :
    indicatorOnSupport E x X e = if e.1 ∈ X then 1 else 0 := by
  unfold indicatorOnSupport; split_ifs <;> simp_all

lemma mem_cut_pair (E : Finset (Sym2 V)) (R : Finset V) (a b : V) :
    s(a, b) ∈ cut E R ↔ s(a, b) ∈ E ∧ ((a ∈ R ∧ b ∉ R) ∨ (b ∈ R ∧ a ∉ R)) := by
  simp only [cut, Finset.mem_filter, Sym2.mem_iff]
  constructor
  · rintro ⟨h, ⟨u, hu, huR⟩, ⟨w, hw, hwR⟩⟩
    refine ⟨h, ?_⟩
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;> tauto
  · rintro ⟨h, (⟨h1, h2⟩ | ⟨h1, h2⟩)⟩
    · exact ⟨h, ⟨a, Or.inl rfl, h1⟩, ⟨b, Or.inr rfl, h2⟩⟩
    · exact ⟨h, ⟨b, Or.inr rfl, h1⟩, ⟨a, Or.inl rfl, h2⟩⟩

lemma mem_internal_pair (E : Finset (Sym2 V)) (R : Finset V) (a b : V) :
    s(a, b) ∈ internal E R ↔ s(a, b) ∈ E ∧ a ∈ R ∧ b ∈ R := by
  simp only [internal, Finset.mem_filter, Sym2.mem_iff]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, h' a (Or.inl rfl), h' b (Or.inr rfl)⟩
  · rintro ⟨h, ha, hb⟩; refine ⟨h, ?_⟩; rintro w (rfl | rfl) <;> assumption

section Pointwise

variable {E F : Finset (Sym2 V)} {x : Sym2 V → ℝ} {L : Finset (Finset V)}

lemma sum_members_mem (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S) (hL : PlusOne.Laminar L)
    {S : Finset V} (hS : S ∈ L) (a : V) :
    ∑ R ∈ members F L S, (if a ∈ R then (1 : ℝ) else 0) = if a ∈ S then 1 else 0 := by
  by_cases ha : a ∈ S
  · obtain ⟨Ra, hRa, haR⟩ := members_cover hLc hS ha
    rw [if_pos ha, Finset.sum_eq_single Ra]
    · rw [if_pos haR]
    · intro R hR hne; rw [if_neg]; intro haR'
      exact hne (members_unique hL hLc hR hRa haR' haR)
    · intro h; exact absurd hRa h
  · rw [if_neg ha]
    refine Finset.sum_eq_zero (fun R hR => ?_)
    rw [if_neg]; intro haR; exact ha (members_subset hR haR)

lemma crossing_pt (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S) (hL : PlusOne.Laminar L)
    {S : Finset V} (hS : S ∈ L) (a b : V) (hsup : s(a, b) ∈ support E x) :
    (if s(a, b) ∈ crossing E F x L S then (1 : ℝ) else 0) +
      ∑ R ∈ members F L S, (if a ∈ R ∧ b ∈ R then (1 : ℝ) else 0) =
      if a ∈ S ∧ b ∈ S then 1 else 0 := by
  have hcr : s(a, b) ∈ crossing E F x L S ↔ ∃ R1 ∈ members F L S, ∃ R2 ∈ members F L S,
      R1 ≠ R2 ∧ a ∈ R1 ∧ b ∈ R2 := by
    unfold crossing
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, R1, h1, R2, h2, hne, u, hu, w, hw, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨R1, h1, R2, h2, hne, hu, hw⟩
      · exact ⟨R2, h2, R1, h1, Ne.symm hne, hw, hu⟩
    · rintro ⟨R1, h1, R2, h2, hne, ha, hb⟩
      exact ⟨hsup, R1, h1, R2, h2, hne, a, ha, b, hb, rfl⟩
  by_cases hab : a ∈ S ∧ b ∈ S
  · rw [if_pos hab]
    obtain ⟨Ra, hRa, haR⟩ := members_cover hLc hS hab.1
    obtain ⟨Rb, hRb, hbR⟩ := members_cover hLc hS hab.2
    by_cases heq : Ra = Rb
    · subst heq
      rw [if_neg, zero_add, Finset.sum_eq_single Ra]
      · rw [if_pos ⟨haR, hbR⟩]
      · intro R hR hne; rw [if_neg]; rintro ⟨haR', _⟩
        exact hne (members_unique hL hLc hR hRa haR' haR)
      · intro h; exact absurd hRa h
      · rw [hcr]; rintro ⟨R1, h1, R2, h2, hne, ha, hb⟩
        exact hne ((members_unique hL hLc h1 hRa ha haR).trans (members_unique hL hLc hRa h2 hbR hb))
    · rw [if_pos (hcr.2 ⟨Ra, hRa, Rb, hRb, heq, haR, hbR⟩), Finset.sum_eq_zero, add_zero]
      intro R hR; rw [if_neg]; rintro ⟨haR', hbR'⟩
      exact heq ((members_unique hL hLc hRa hR haR haR').trans (members_unique hL hLc hR hRb hbR' hbR))
  · rw [if_neg hab, if_neg, zero_add]
    · refine Finset.sum_eq_zero (fun R hR => ?_)
      rw [if_neg]; rintro ⟨haR, hbR⟩
      exact hab ⟨members_subset hR haR, members_subset hR hbR⟩
    · rw [hcr]; rintro ⟨R1, h1, R2, h2, _, ha, hb⟩
      exact hab ⟨members_subset h1 ha, members_subset h2 hb⟩

/-- Pointwise identities on support edges. -/
lemma pt_identities (hLc : ∀ S ∈ L, S.Nonempty ∧ Compatible F S) (hL : PlusOne.Laminar L)
    {S : Finset V} (hS : S ∈ L) (e : Sym2 V) (hsup : e ∈ support E x) :
    ((if e ∈ internal E S then (1 : ℝ) else 0) = (if e ∈ crossing E F x L S then 1 else 0) +
      ∑ R ∈ members F L S, (if e ∈ internal E R then (1 : ℝ) else 0)) ∧
    (∑ R ∈ members F L S, (if e ∈ cut E R then (1 : ℝ) else 0) =
      2 * (if e ∈ crossing E F x L S then 1 else 0) + (if e ∈ cut E S then 1 else 0)) := by
  have hEe : e ∈ E := by simp only [support, Finset.mem_filter] at hsup; exact hsup.1
  induction e using Sym2.ind with
  | _ a b =>
  have hc := crossing_pt hLc hL hS a b hsup
  have hint : ∀ R : Finset V, (if s(a, b) ∈ internal E R then (1 : ℝ) else 0) =
      if a ∈ R ∧ b ∈ R then 1 else 0 := by
    intro R
    by_cases h : a ∈ R ∧ b ∈ R
    · rw [if_pos h, if_pos ((mem_internal_pair E R a b).2 ⟨hEe, h⟩)]
    · rw [if_neg h, if_neg]; intro h'; exact h ((mem_internal_pair E R a b).1 h').2
  have hcut : ∀ R : Finset V, (if s(a, b) ∈ cut E R then (1 : ℝ) else 0) =
      (if a ∈ R then 1 else 0) + (if b ∈ R then 1 else 0) - 2 * (if a ∈ R ∧ b ∈ R then 1 else 0) := by
    intro R
    by_cases ha : a ∈ R <;> by_cases hb : b ∈ R <;> simp [ha, hb, hEe, mem_cut_pair] <;> norm_num
  constructor
  · rw [hint S, ← hc]
    congr 1
    exact Finset.sum_congr rfl (fun R _ => (hint R).symm)
  · rw [Finset.sum_congr rfl (fun R _ => hcut R), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_members_mem hLc hL hS a, sum_members_mem hLc hL hS b, hcut S]
    have : (if s(a, b) ∈ crossing E F x L S then (1 : ℝ) else 0) =
        (if a ∈ S ∧ b ∈ S then 1 else 0) -
          ∑ R ∈ members F L S, (if a ∈ R ∧ b ∈ R then (1 : ℝ) else 0) := by linarith
    rw [this]; ring

end Pointwise

lemma mem_cut_support_iff (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (X : Finset V) {f : Sym2 V}
    (hf : f ∈ support E x) : f ∈ cut E X ↔ f ∈ cut (support E x) X := by
  simp only [support, Finset.mem_filter] at hf
  simp only [cut, support, Finset.mem_filter]
  tauto

lemma cut_support_eq_inter (E : Finset (Sym2 V)) (x : Sym2 V → ℝ) (X : Finset V) :
    cut (support E x) X = support E x ∩ cut E X := by
  ext f
  rw [Finset.mem_inter]
  constructor
  · intro h
    have hf := cut_subset _ _ h
    exact ⟨hf, (mem_cut_support_iff E x X hf).2 h⟩
  · rintro ⟨hf, h⟩; exact (mem_cut_support_iff E x X hf).1 h

lemma special_supernode_facts (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E)
    (hbasic : Basic E A B U W F x)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (C : Finset V) (hC : IsSpecialSupernode E F x (TU ∪ TW) C) :
    ∃ v ∈ C, v ∈ TU ∪ TW ∧ cut (support E x) C = (support E x).filter (fun f => v ∈ f) ∧
      degree (support E x) v = 3 ∧
      (PlusOne.edgeSum x (cut E C) = 1 ∨ PlusOne.edgeSum x (cut E C) = 2) := by
  have hfeas := hbasic.1
  obtain ⟨v, hvC, hva, huniq, hvT, hdeg⟩ := claim_5_4_core E F A B U W x L TU TW hE hbasic hbasis
    hnoone hnodeg2 C hC
  obtain ⟨v0, rfl⟩ := (mem_supernodes_iff F C).1 hC.1
  have tight := supernode_tight hfeas v0
  have hZ : ∀ e ∈ internal E (supernodeOf F v0), x e = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun e he => hfeas.2.2.2.2.2 e (internal_subset E _ he))).1 tight.1
  have hcut : cut (support E x) (supernodeOf F v0) = (support E x).filter (fun f => v ∈ f) := by
    ext f
    rw [Finset.mem_filter]
    constructor
    · intro hf
      have hfs : f ∈ support E x := cut_subset _ _ hf
      simp only [cut, Finset.mem_filter] at hf
      obtain ⟨_, ⟨u, hu, huC⟩, _⟩ := hf
      have := huniq u huC (active_of_mem E x hfs hu)
      subst this
      exact ⟨hfs, hu⟩
    · rintro ⟨hfs, hvf⟩
      simp only [cut, Finset.mem_filter]
      refine ⟨hfs, ⟨v, hvf, hvC⟩, ?_⟩
      by_contra hall
      push_neg at hall
      have hfE : f ∈ E := by simp only [support, Finset.mem_filter] at hfs; exact hfs.1
      have hne : x f ≠ 0 := by simp only [support, Finset.mem_filter] at hfs; exact hfs.2
      apply hne; apply hZ
      simp only [internal, Finset.mem_filter]
      exact ⟨hfE, hall⟩
  refine ⟨v, hvC, hvT, hcut, hdeg, ?_⟩
  -- the value
  obtain ⟨k, hk⟩ : ∃ k : ℤ, PlusOne.edgeSum x (cut E {v}) = (k : ℝ) := by
    rcases Finset.mem_union.1 hvT with h | h
    · exact ⟨A v, hbasis.2.2.2.2.2.1 v h⟩
    · exact ⟨B v, hbasis.2.2.2.2.2.2.1 v h⟩
  rw [edgeSum_support, cut_single_support E x hE] at hk
  rw [edgeSum_support, hcut]
  have hcard : ((support E x).filter (fun f => v ∈ f)).card = 3 := by
    rw [← degree_eq_card_of (support E x) v _ (fun f => Finset.mem_filter)]; exact hdeg
  have hpos : ∀ f ∈ (support E x).filter (fun f => v ∈ f), 0 < x f ∧ x f < 1 := by
    intro f hf
    have hfs := (Finset.mem_filter.1 hf).1
    have hfE : f ∈ E := by simp only [support, Finset.mem_filter] at hfs; exact hfs.1
    have hne : x f ≠ 0 := by simp only [support, Finset.mem_filter] at hfs; exact hfs.2
    exact ⟨lt_of_le_of_ne (hfeas.2.2.2.2.2 f hfE) (Ne.symm hne),
      lt_of_le_of_ne (x_le_one hE hfeas hfE) (hnoone f hfs)⟩
  have hne : ((support E x).filter (fun f => v ∈ f)).Nonempty := by
    rw [← Finset.card_pos, hcard]; norm_num
  have h0 : 0 < PlusOne.edgeSum x ((support E x).filter (fun f => v ∈ f)) :=
    Finset.sum_pos (fun f hf => (hpos f hf).1) hne
  have h3 : PlusOne.edgeSum x ((support E x).filter (fun f => v ∈ f)) < 3 := by
    have := Finset.sum_lt_sum_of_nonempty hne (fun f hf => (hpos f hf).2)
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, mul_one] at this
    unfold PlusOne.edgeSum; push_cast at this; linarith
  rw [hk] at h0 h3 ⊢
  have : (0 : ℤ) < k := by exact_mod_cast h0
  have : k < (3 : ℤ) := by exact_mod_cast h3
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl
  · left; norm_num
  · right; norm_num

theorem claim_5_9_core
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ)
    (hthree : (members F L S).card = 3)
    (hspecial : ∀ R ∈ members F L S, IsSpecialMember E F x L (TU ∪ TW) R)
    (hD : 3 ≤ (crossing E F x L S).card) :
    IsSpecialSet E x L (TU ∪ TW) S := by
  have hfeas := hbasic.1
  have hL := hbasis.2.1
  have hLc := hbasis.2.2.1
  set M := members F L S with hM
  set T := TU ∪ TW with hT
  set SP := Submodule.span ℝ
    ((fun R => indicatorOnSupport E x (internal E R)) '' {R | R ∈ L ∧ R ⊆ S} ∪
     (fun v => indicatorOnSupport E x (cut E {v})) '' {v | v ∈ S ∧ v ∈ T}) with hSP
  -- facts on members
  have hfacts : ∀ R ∈ M, (cut (support E x) R).card = 3 ∧
      (PlusOne.edgeSum x (cut E R) = 1 ∨ PlusOne.edgeSum x (cut E R) = 2) ∧
      indicatorOnSupport E x (cut E R) ∈ SP := by
    intro R hR
    have hRS : R ⊆ S := members_subset hR
    rcases hspecial R hR with hsn | hss
    · obtain ⟨v, hvC, hvT, hcut, hdeg, hval⟩ := special_supernode_facts E F A B U W x L TU TW hE
        hbasic hbasis hnoone hnodeg2 R hsn
      refine ⟨?_, hval, ?_⟩
      · rw [hcut, ← degree_eq_card_of (support E x) v _ (fun f => Finset.mem_filter)]; exact hdeg
      · have : indicatorOnSupport E x (cut E R) = indicatorOnSupport E x (cut E {v}) := by
          funext e
          rw [ind_val, ind_val]
          have h1 := mem_cut_support_iff E x R e.2
          have h2 := mem_cut_support_iff E x {v} e.2
          rw [cut_single_support E x hE] at h2
          rw [hcut] at h1
          have : e.1 ∈ cut E R ↔ e.1 ∈ cut E {v} := by rw [h1, h2]
          by_cases h : e.1 ∈ cut E R
          · rw [if_pos h, if_pos (this.1 h)]
          · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]
        rw [this]
        exact Submodule.subset_span (Set.mem_union_right _ ⟨v, ⟨hRS hvC, hvT⟩, rfl⟩)
    · refine ⟨hss.2.1, hss.2.2.1, ?_⟩
      refine Submodule.span_mono ?_ hss.2.2.2
      apply Set.union_subset_union
      · apply Set.image_mono
        intro R' hR'; exact ⟨hR'.1, hR'.2.trans hRS⟩
      · apply Set.image_mono
        intro v hv; exact ⟨hRS hv.1, hv.2⟩
  -- weighted counting
  have hweight : ∀ g : Sym2 V → ℝ,
      ∑ R ∈ M, ∑ e ∈ cut (support E x) R, g e =
        2 * ∑ e ∈ crossing E F x L S, g e + ∑ e ∈ cut (support E x) S, g e := by
    intro g
    have hX : ∀ X : Finset V, ∑ e ∈ cut (support E x) X, g e =
        ∑ e ∈ support E x, (if e ∈ cut E X then (1 : ℝ) else 0) * g e := by
      intro X
      simp only [boole_mul]
      rw [Finset.sum_ite_mem, cut_support_eq_inter]
    have hDsub : crossing E F x L S ⊆ support E x := by
      intro e he; unfold crossing at he; exact (Finset.mem_filter.1 he).1
    have hDs : ∑ e ∈ crossing E F x L S, g e =
        ∑ e ∈ support E x, (if e ∈ crossing E F x L S then (1 : ℝ) else 0) * g e := by
      simp only [boole_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hDsub]
    simp only [hX, hDs]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e he => ?_)
    rw [← Finset.sum_mul, (pt_identities hLc hL hS e he).2]
    ring
  -- card
  have hc := hweight (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [Finset.sum_congr rfl (fun R hR => by rw [(hfacts R hR).1])] at hc
  simp only [Finset.sum_const, nsmul_eq_mul, hthree] at hc
  have hcN : (cut (support E x) S).card + 2 * (crossing E F x L S).card = 9 := by
    have : ((cut (support E x) S).card : ℝ) + 2 * (crossing E F x L S).card = 9 := by
      push_cast at hc ⊢; linarith
    exact_mod_cast this
  have h57 := claim_5_7_core E F A B U W x L TU TW hE hF hEF hbasic hnotree hbasis hnoone hnodeg2
    S hS hSV
  have hcut3 : (cut (support E x) S).card = 3 := by omega
  refine ⟨hSV, hcut3, ?_, ?_⟩
  · -- value
    have hxw := hweight x
    have h58 := claim_5_8_core E F A B U W x L TU TW hfeas hbasis S hS
    rw [← hM, hthree] at h58
    unfold PlusOne.edgeSum at h58
    rw [h58] at hxw
    have hcutR : ∀ R ∈ M, ∑ e ∈ cut (support E x) R, x e = PlusOne.edgeSum x (cut E R) := by
      intro R _; rw [edgeSum_support]; rfl
    rw [Finset.sum_congr rfl hcutR] at hxw
    have hpos : 0 < PlusOne.edgeSum x (cut E S) := by
      rw [edgeSum_support]
      have hne : (cut (support E x) S).Nonempty := by rw [← Finset.card_pos, hcut3]; norm_num
      refine Finset.sum_pos (fun f hf => ?_) hne
      have hfs := cut_subset _ _ hf
      have hfE : f ∈ E := by simp only [support, Finset.mem_filter] at hfs; exact hfs.1
      have hne : x f ≠ 0 := by simp only [support, Finset.mem_filter] at hfs; exact hfs.2
      exact lt_of_le_of_ne (hfeas.2.2.2.2.2 f hfE) (Ne.symm hne)
    have hxS : PlusOne.edgeSum x (cut E S) = ∑ e ∈ cut (support E x) S, x e := by
      rw [edgeSum_support]; rfl
    rw [← hxS] at hxw
    obtain ⟨R1, R2, R3, h12, h13, h23, hMeq⟩ := Finset.card_eq_three.1 hthree
    have hR1 : R1 ∈ M := by rw [hMeq]; simp
    have hR2 : R2 ∈ M := by rw [hMeq]; simp
    have hR3 : R3 ∈ M := by rw [hMeq]; simp
    rw [hMeq, Finset.sum_insert (by simp [h12, h13]), Finset.sum_insert (by simp [h23]),
      Finset.sum_singleton] at hxw
    have f1 := (hfacts R1 hR1).2.1
    have f2 := (hfacts R2 hR2).2.1
    have f3 := (hfacts R3 hR3).2.1
    norm_num at hxw
    rcases f1 with f1 | f1 <;> rcases f2 with f2 | f2 <;> rcases f3 with f3 | f3 <;>
      first
        | (left; linarith)
        | (right; linarith)
        | (exfalso; linarith)
  · -- span
    have hvec : indicatorOnSupport E x (cut E S) =
        (∑ R ∈ M, indicatorOnSupport E x (cut E R)) -
          (2 : ℝ) • indicatorOnSupport E x (internal E S) +
          (2 : ℝ) • ∑ R ∈ M, indicatorOnSupport E x (internal E R) := by
      funext e
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ind_val]
      have p := pt_identities hLc hL hS e.1 e.2
      rw [p.1] at ⊢
      linarith [p.2]
    rw [hvec]
    refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.sum_mem _ (fun R hR => (hfacts R hR).2.2)
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_union_left _ ⟨S, ⟨hS, subset_refl S⟩, rfl⟩))
    · refine Submodule.sum_mem _ (fun R hR => ?_)
      have hR' := hR
      rw [hM, mem_members_iff] at hR'
      rcases hR' with hch | hsn
      · exact Submodule.subset_span (Set.mem_union_left _ ⟨R, ⟨hch.1, hch.2.1.1⟩, rfl⟩)
      · obtain ⟨u, rfl⟩ := (mem_supernodes_iff F _).1 hsn.1
        have t := supernode_tight hfeas u
        have hZ : ∀ e ∈ internal E (supernodeOf F u), x e = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun e he => hfeas.2.2.2.2.2 e (internal_subset E _ he))).1 t.1
        have : indicatorOnSupport E x (internal E (supernodeOf F u)) = 0 := by
          funext e
          rw [ind_val, Pi.zero_apply, if_neg]
          intro he
          have hne : x e.1 ≠ 0 := by
            have := e.2; simp only [support, Finset.mem_filter] at this; exact this.2
          exact hne (hZ _ he)
        rw [this]; exact Submodule.zero_mem _

end BoundedDegreeST.LowerUpper

open BoundedDegreeST.LowerUpper


theorem solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (E F : Finset (Sym2 V)) (A B : V → ℤ) (U W : Finset V)
    (x : Sym2 V → ℝ) (L : Finset (Finset V)) (TU TW : Finset V)
    (hE : BoundedDegreeST.PlusOne.SimpleEdges E) (hF : BoundedDegreeST.PlusOne.IsForest F) (hEF : Disjoint E F)
    (hbasic : Basic E A B U W F x) (hnotree : ¬ BoundedDegreeST.PlusOne.IsSpanningTree F)
    (hbasis : DefinesBasis E A B U W F x L TU TW)
    (hnoone : ∀ e ∈ support E x, x e ≠ 1)
    (hnodeg2 : ∀ v ∈ U ∪ W, degree (support E x) v ≠ 2)
    (S : Finset V) (hS : S ∈ L) (hSV : S ≠ Finset.univ)
    (hthree : (members F L S).card = 3)
    (hspecial : ∀ R ∈ members F L S, IsSpecialMember E F x L (TU ∪ TW) R)
    (hD : 3 ≤ (crossing E F x L S).card) :
    IsSpecialSet E x L (TU ∪ TW) S := by
  exact claim_5_9_core E F A B U W x L TU TW hE hF hEF hbasic hnotree hbasis hnoone hnodeg2 S hS hSV hthree hspecial hD
