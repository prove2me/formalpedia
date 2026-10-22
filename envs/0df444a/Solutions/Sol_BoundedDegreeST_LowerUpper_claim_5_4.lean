-- Prove2me | solution 1 for BoundedDegreeST.LowerUpper.claim_5_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:54:31.125651+00:00
-- url     : https://prove2.me/submissions/b750e46b-5fff-43bb-b9d0-a2c56ae2be8b

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
    (C : Finset V) (hC : IsSpecialSupernode E F x (TU ∪ TW) C) :
    ∃ v ∈ C, Active E x v ∧ (∀ w ∈ C, Active E x w → w = v) ∧
      v ∈ TU ∪ TW ∧ degree (support E x) v = 3 := by
  exact claim_5_4_core E F A B U W x L TU TW hE hbasic hbasis hnoone hnodeg2 C hC
