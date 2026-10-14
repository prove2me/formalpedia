-- Prove2me | solution 1 for CooperationGraphs.FairRule.restrict_removeLink_le
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:12:01.705504+00:00
-- url     : https://prove2.me/submissions/3a7acf55-9db8-4ae4-8276-f2b40f320b0a

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic



namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

theorem rtg_mono {α : Type*} {r p : α → α → Prop} (h : ∀ x y, r x y → p x y) {a b : α}
    (hr : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact ih.tail (h _ _ h2)

theorem rtg_symm {α : Type*} {r : α → α → Prop} (hs : ∀ x y, r x y → r y x) {a b : α}
    (hr : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih => exact Relation.ReflTransGen.head (hs _ _ h2) ih

section Basics
variable {n : ℕ}

/-- class of `j` in `S` under `g` -/
noncomputable def cls (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) (j : Fin n) : Finset (Fin n) :=
  S.filter (fun i => ConnectedIn g S i j)

lemma connectedIn_refl {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {a : Fin n} (h : a ∈ S) :
    ConnectedIn g S a a := ⟨h, h, Relation.ReflTransGen.refl⟩

lemma connectedIn_symm {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {a b : Fin n}
    (h : ConnectedIn g S a b) : ConnectedIn g S b a := by
  obtain ⟨ha, hb, hr⟩ := h
  refine ⟨hb, ha, ?_⟩
  exact rtg_symm (fun x y hxy => ⟨hxy.2.1, hxy.1, hxy.2.2.symm⟩) hr

lemma connectedIn_trans {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {a b c : Fin n}
    (h1 : ConnectedIn g S a b) (h2 : ConnectedIn g S b c) : ConnectedIn g S a c :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

lemma connectedIn_mono_graph {g g' : SimpleGraph (Fin n)} (hg : g ≤ g') {S : Finset (Fin n)}
    {a b : Fin n} (h : ConnectedIn g S a b) : ConnectedIn g' S a b :=
  ⟨h.1, h.2.1, rtg_mono (fun x y hxy => ⟨hxy.1, hxy.2.1, hg hxy.2.2⟩) h.2.2⟩

lemma mem_cls {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {i j : Fin n} :
    i ∈ cls g S j ↔ ConnectedIn g S i j := by
  unfold cls
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

lemma mem_quot {g : SimpleGraph (Fin n)} {S B : Finset (Fin n)} :
    B ∈ quot S g ↔ ∃ j ∈ S, B = cls g S j := by
  unfold quot
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, h.symm⟩
  · rintro ⟨j, hj, h⟩; exact ⟨j, hj, h.symm⟩

lemma cls_mem_quot {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    cls g S j ∈ quot S g := mem_quot.2 ⟨j, hj, rfl⟩

lemma self_mem_cls {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    j ∈ cls g S j := mem_cls.2 (connectedIn_refl hj)

lemma cls_eq_of_conn {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {i j : Fin n}
    (h : ConnectedIn g S i j) : cls g S i = cls g S j := by
  ext x
  rw [mem_cls, mem_cls]
  exact ⟨fun hx => connectedIn_trans hx h, fun hx => connectedIn_trans hx (connectedIn_symm h)⟩

lemma quot_eq_cls {g : SimpleGraph (Fin n)} {S B : Finset (Fin n)} (hB : B ∈ quot S g) {x : Fin n}
    (hx : x ∈ B) : B = cls g S x := by
  obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
  exact (cls_eq_of_conn (mem_cls.1 hx)).symm

lemma quot_subset {g : SimpleGraph (Fin n)} {S B : Finset (Fin n)} (hB : B ∈ quot S g) : B ⊆ S := by
  obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
  intro x hx
  exact (mem_cls.1 hx).1

lemma quot_nonempty {g : SimpleGraph (Fin n)} {S B : Finset (Fin n)} (hB : B ∈ quot S g) :
    B.Nonempty := by
  obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
  exact ⟨j, self_mem_cls hj⟩

lemma quot_disjoint {g : SimpleGraph (Fin n)} {S B B' : Finset (Fin n)} (hB : B ∈ quot S g)
    (hB' : B' ∈ quot S g) (hne : B ≠ B') : Disjoint B B' := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact hne ((quot_eq_cls hB hx).trans (quot_eq_cls hB' hx').symm)

lemma quot_pairwiseDisjoint (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    Set.PairwiseDisjoint (↑(quot S g) : Set (Finset (Fin n))) id :=
  fun _ hB _ hB' hne => quot_disjoint hB hB' hne

lemma exists_quot_of_mem {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} {x : Fin n} (hx : x ∈ S) :
    ∃ B ∈ quot S g, x ∈ B := ⟨cls g S x, cls_mem_quot hx, self_mem_cls hx⟩

lemma quot_biUnion (g : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    (quot S g).biUnion id = S := by
  ext x
  simp only [Finset.mem_biUnion, id]
  constructor
  · rintro ⟨B, hB, hx⟩; exact quot_subset hB hx
  · intro hx; exact exists_quot_of_mem hx

lemma quot_empty (g : SimpleGraph (Fin n)) : quot ∅ g = ∅ := by
  simp [quot]

lemma restrict_empty (v : Game n) (g : SimpleGraph (Fin n)) : restrict v g ∅ = 0 := by
  simp [restrict, quot_empty]

lemma quot_nonempty_set {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} (hS : S.Nonempty) :
    (quot S g).Nonempty := by
  obtain ⟨x, hx⟩ := hS
  exact ⟨_, cls_mem_quot hx⟩

/-- removeLink adjacency -/
lemma removeLink_adj {g : SimpleGraph (Fin n)} {a b x y : Fin n} :
    (removeLink g a b).Adj x y ↔ g.Adj x y ∧ s(x, y) ≠ s(a, b) := by
  unfold removeLink
  rw [SimpleGraph.deleteEdges_adj]
  simp

lemma removeLink_le (g : SimpleGraph (Fin n)) (a b : Fin n) : removeLink g a b ≤ g :=
  SimpleGraph.deleteEdges_le _

lemma removeLink_lt {g : SimpleGraph (Fin n)} {a b : Fin n} (hab : g.Adj a b) :
    removeLink g a b < g := by
  refine lt_of_le_of_ne (removeLink_le g a b) ?_
  intro h
  have : (removeLink g a b).Adj a b := by rw [h]; exact hab
  rw [removeLink_adj] at this
  exact this.2 rfl

lemma connectedIn_removeLink {g : SimpleGraph (Fin n)} {a b : Fin n} {S : Finset (Fin n)}
    (hS : a ∉ S ∨ b ∉ S) {x y : Fin n} :
    ConnectedIn (removeLink g a b) S x y ↔ ConnectedIn g S x y := by
  constructor
  · exact connectedIn_mono_graph (removeLink_le g a b)
  · rintro ⟨hx, hy, hr⟩
    refine ⟨hx, hy, rtg_mono ?_ hr⟩
    rintro u v ⟨hu, hv, huv⟩
    refine ⟨hu, hv, removeLink_adj.2 ⟨huv, ?_⟩⟩
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rcases hS with h | h <;> contradiction
    · subst h1; subst h2; rcases hS with h | h <;> contradiction

lemma quot_removeLink_of {g : SimpleGraph (Fin n)} {a b : Fin n} {S : Finset (Fin n)}
    (hS : a ∉ S ∨ b ∉ S) : quot S (removeLink g a b) = quot S g := by
  unfold quot
  apply Finset.image_congr
  intro j _
  apply Finset.filter_congr
  intro i _
  exact connectedIn_removeLink hS

lemma quot_removeLink_refines_core (g : SimpleGraph (Fin n)) (a b : Fin n) (S : Finset (Fin n)) :
    (∀ B ∈ quot S (removeLink g a b), ∃ C ∈ quot S g, B ⊆ C) ∧
      (a ∉ S → quot S (removeLink g a b) = quot S g) := by
  refine ⟨?_, fun h => quot_removeLink_of (Or.inl h)⟩
  intro B hB
  obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
  refine ⟨cls g S j, cls_mem_quot hj, ?_⟩
  intro x hx
  exact mem_cls.2 (connectedIn_mono_graph (removeLink_le g a b) (mem_cls.1 hx))

lemma super_sum {v : Game n} (hv : IsSuperadditive v) :
    ∀ F : Finset (Finset (Fin n)), F.Nonempty → (∀ B ∈ F, B.Nonempty) →
      Set.PairwiseDisjoint (↑F : Set (Finset (Fin n))) id →
      ∑ B ∈ F, v B ≤ v (F.biUnion id) := by
  intro F
  induction F using Finset.induction_on with
  | empty => intro h; exact absurd h (by simp)
  | insert B F hB ih =>
    intro _ hne hdis
    by_cases hF : F.Nonempty
    · rw [Finset.sum_insert hB, Finset.biUnion_insert]
      have h1 := ih hF (fun C hC => hne C (Finset.mem_insert_of_mem hC))
        (hdis.subset (by intro x hx; exact Finset.mem_insert_of_mem hx))
      have h2 : Disjoint B (F.biUnion id) := by
        rw [Finset.disjoint_biUnion_right]
        intro C hC
        exact hdis (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hC)
          (fun h => hB (h ▸ hC))
      have h3 : (F.biUnion id).Nonempty := by
        obtain ⟨C, hC⟩ := hF
        obtain ⟨x, hx⟩ := hne C (Finset.mem_insert_of_mem hC)
        exact ⟨x, Finset.mem_biUnion.2 ⟨C, hC, hx⟩⟩
      have h4 := hv B (F.biUnion id) (hne B (Finset.mem_insert_self _ _)) h3 h2
      simp only [id] at h4 ⊢
      linarith
    · have : F = ∅ := Finset.not_nonempty_iff_eq_empty.1 hF
      subst this
      simp

lemma restrict_removeLink_le_core (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (S : Finset (Fin n)) (hS : S.Nonempty) :
    restrict v (removeLink g a b) S ≤ restrict v g S ∧
      (a ∉ S → restrict v (removeLink g a b) S = restrict v g S) := by
  refine ⟨?_, fun h => by unfold restrict; rw [quot_removeLink_of (Or.inl h)]⟩
  unfold restrict
  have hex := (quot_removeLink_refines_core g a b S).1
  choose! f hfmem hfsub using hex
  rw [← Finset.sum_fiberwise_of_maps_to (s := quot S (removeLink g a b)) (t := quot S g)
    (g := f) (fun B hB => hfmem B hB)]
  apply Finset.sum_le_sum
  intro C hC
  have hCne : C.Nonempty := quot_nonempty hC
  have hunion : ((quot S (removeLink g a b)).filter (fun B => f B = C)).biUnion id = C := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_filter, id]
    constructor
    · rintro ⟨B, ⟨hB, hfB⟩, hx⟩
      rw [← hfB]; exact hfsub B hB hx
    · intro hx
      have hxS : x ∈ S := quot_subset hC hx
      refine ⟨cls (removeLink g a b) S x, ⟨cls_mem_quot hxS, ?_⟩, self_mem_cls hxS⟩
      have h1 := hfsub _ (cls_mem_quot hxS) (self_mem_cls hxS)
      have h2 := hfmem _ (cls_mem_quot hxS)
      by_contra hne
      have := quot_disjoint h2 hC hne
      exact (Finset.disjoint_left.1 this) h1 hx
  have hfne : ((quot S (removeLink g a b)).filter (fun B => f B = C)).Nonempty := by
    obtain ⟨x, hx⟩ := hCne
    have hxS : x ∈ S := quot_subset hC hx
    refine ⟨cls (removeLink g a b) S x, Finset.mem_filter.2 ⟨cls_mem_quot hxS, ?_⟩⟩
    have h1 := hfsub _ (cls_mem_quot hxS) (self_mem_cls hxS)
    have h2 := hfmem _ (cls_mem_quot hxS)
    by_contra hne
    have := quot_disjoint h2 hC hne
    exact (Finset.disjoint_left.1 this) h1 hx
  have := super_sum hv _ hfne
    (fun B hB => quot_nonempty (Finset.mem_filter.1 hB).1)
    ((quot_pairwiseDisjoint _ _).subset (by intro x hx; exact (Finset.mem_filter.1 hx).1))
  rwa [hunion] at this

end Basics
section Shap
variable {n : ℕ}

open Supermodularity.Cooperative in
/-- weight -/
noncomputable def cc (n k : ℕ) : ℝ := (k.factorial * (n - k - 1).factorial : ℝ) / n.factorial

lemma shapleyValue_def (f : Finset (Fin n) → ℝ) (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue f i =
      ∑ S ∈ (Finset.univ.erase i).powerset, cc n S.card * (f (insert i S) - f S) := rfl

lemma shap_coeff (f : Finset (Fin n) → ℝ) (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue f i =
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => i ∈ U), cc n (U.card - 1) * f U
      - ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => i ∉ U), cc n U.card * f U := by
  rw [shapleyValue_def]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  · refine Finset.sum_nbij' (fun S => insert i S) (fun U => U.erase i) ?_ ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_powerset, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and, Finset.subset_univ, and_true] at hS ⊢
      exact Finset.mem_insert_self _ _
    · intro U hU
      exact Finset.mem_powerset.2 (Finset.erase_subset_erase i (Finset.subset_univ U))
    · intro S hS
      have : i ∉ S := by
        intro h
        have := Finset.mem_powerset.1 hS h
        simp at this
      exact Finset.erase_insert this
    · intro U hU
      have : i ∈ U := (Finset.mem_filter.1 hU).2
      exact Finset.insert_erase this
    · intro S hS
      have : i ∉ S := by
        intro h
        have := Finset.mem_powerset.1 hS h
        simp at this
      rw [Finset.card_insert_of_notMem this]
      simp
  · have : (Finset.univ.erase i).powerset =
        (Finset.univ : Finset (Fin n)).powerset.filter (fun U => i ∉ U) := by
      ext S
      simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_univ, true_and]
      constructor
      · intro h hi
        have := h hi
        simp at this
      · intro h x hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        rintro rfl
        exact h hx
    rw [this]

lemma shap_sub (f f' : Finset (Fin n) → ℝ) (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue (fun S => f S - f' S) i =
      Supermodularity.Cooperative.ShapleyValue f i - Supermodularity.Cooperative.ShapleyValue f' i := by
  simp only [shapleyValue_def, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  ring

lemma shap_sum_fun {ι : Type*} (𝒯 : Finset ι) (f : ι → Finset (Fin n) → ℝ) (i : Fin n) :
    Supermodularity.Cooperative.ShapleyValue (fun S => ∑ T ∈ 𝒯, f T S) i =
      ∑ T ∈ 𝒯, Supermodularity.Cooperative.ShapleyValue (f T) i := by
  simp only [shapleyValue_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

lemma shap_null (f : Finset (Fin n) → ℝ) (i : Fin n)
    (h : ∀ U : Finset (Fin n), i ∉ U → f (insert i U) = f U) :
    Supermodularity.Cooperative.ShapleyValue f i = 0 := by
  rw [shapleyValue_def]
  apply Finset.sum_eq_zero
  intro S hS
  have : i ∉ S := by
    intro hi
    have := Finset.mem_powerset.1 hS hi
    simp at this
  rw [h S this]; ring

lemma coef_k (n k : ℕ) (hn : 0 < n) (hk : k ≤ n) :
    (k : ℝ) * cc n (k - 1) - ((n - k : ℕ) : ℝ) * cc n k =
      (if k = n then 1 else 0) - (if k = 0 then 1 else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp [cc, Nat.factorial_succ]
    field_simp
  rcases Nat.lt_or_ge k (m + 1) with hlt | hge
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r, m = j + r + 1 := ⟨m - j - 1, by omega⟩
    subst hr
    have h1 : (j + r + 1 + 1 - (j + 1)) = r + 1 := by omega
    have h2 : (j + r + 1 + 1 - j - 1) = r + 1 := by omega
    have h3 : (j + r + 1 + 1 - (j + 1) - 1) = r := by omega
    simp only [cc, Nat.add_sub_cancel, h1, h2, h3]
    have hne : (j + 1 = j + r + 1 + 1) = False := by
      simp only [eq_iff_iff, iff_false]; omega
    simp only [hne, if_false, Nat.succ_ne_zero]
    rw [Nat.factorial_succ j, Nat.factorial_succ r]
    push_cast
    field_simp
    ring
  · have : k = m + 1 := le_antisymm hk hge
    subst this
    simp [cc, Nat.factorial_succ]
    field_simp

lemma shap_efficiency (hn : 0 < n) (f : Finset (Fin n) → ℝ) :
    ∑ i, Supermodularity.Cooperative.ShapleyValue f i = f Finset.univ - f ∅ := by
  simp only [shap_coeff, Finset.sum_sub_distrib]
  have e1 : ∑ i : Fin n, ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => i ∈ U),
      cc n (U.card - 1) * f U =
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset, (U.card : ℝ) * (cc n (U.card - 1) * f U) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ i : Fin n, ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => i ∉ U),
      cc n U.card * f U =
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset,
        ((n - U.card : ℕ) : ℝ) * (cc n U.card * f U) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : (Finset.univ.filter (fun i : Fin n => i ∉ U)) = Uᶜ := by ext; simp
    rw [this, Finset.card_compl, Fintype.card_fin]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  have e3 : ∀ U ∈ (Finset.univ : Finset (Fin n)).powerset,
      (U.card : ℝ) * (cc n (U.card - 1) * f U) - ((n - U.card : ℕ) : ℝ) * (cc n U.card * f U) =
      ((if U = Finset.univ then (1 : ℝ) else 0) - (if U = ∅ then 1 else 0)) * f U := by
    intro U _
    have hc := coef_k n U.card hn (by simpa using Finset.card_le_univ U)
    have h1 : (U = Finset.univ) ↔ U.card = n := by
      rw [← Finset.card_eq_iff_eq_univ, Fintype.card_fin]
    have h2 : (U = ∅) ↔ U.card = 0 := Finset.card_eq_zero.symm
    simp only [h1, h2]
    rw [← hc]; ring
  rw [Finset.sum_congr rfl e3]
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  simp [Finset.sum_ite_eq']

end Shap
section Main
variable {n : ℕ}

lemma shapley_eq_of_empty (w : Game n) (h : w ∅ = 0) :
    shapley w = Supermodularity.Cooperative.ShapleyValue w := by
  unfold shapley
  rw [Function.update_eq_self_iff.2 h.symm]

lemma uGame_empty (v : Game n) (g : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    uGame v g T ∅ = 0 := by
  simp [uGame, quot_empty]

lemma connectedIn_mono_set {g : SimpleGraph (Fin n)} {S S' : Finset (Fin n)} (hS : S ⊆ S')
    {a b : Fin n} (h : ConnectedIn g S a b) : ConnectedIn g S' a b :=
  ⟨hS h.1, hS h.2.1, rtg_mono
    (fun _ _ hxy => ⟨hS hxy.1, hS hxy.2.1, hxy.2.2⟩) h.2.2⟩

lemma mem_K_of_path {g : SimpleGraph (Fin n)} {T : Finset (Fin n)} {x j : Fin n}
    (h : Relation.ReflTransGen (fun x y => x ∈ T ∧ y ∈ T ∧ g.Adj x y) x j) :
    ConnectedIn g Finset.univ x j :=
  ⟨Finset.mem_univ _, Finset.mem_univ _,
    rtg_mono (fun _ _ h => ⟨Finset.mem_univ _, Finset.mem_univ _, h.2.2⟩) h⟩

lemma path_inter {g : SimpleGraph (Fin n)} {T : Finset (Fin n)} {j x : Fin n}
    (hr : Relation.ReflTransGen (fun x y => x ∈ T ∧ y ∈ T ∧ g.Adj x y) x j) :
    Relation.ReflTransGen
      (fun x y => x ∈ T ∩ cls g Finset.univ j ∧ y ∈ T ∩ cls g Finset.univ j ∧ g.Adj x y) x j := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hac hcb ih =>
    refine Relation.ReflTransGen.head ⟨?_, ?_, hac.2.2⟩ ih
    · exact Finset.mem_inter.2 ⟨hac.1,
        mem_cls.2 (mem_K_of_path (Relation.ReflTransGen.head hac hcb))⟩
    · exact Finset.mem_inter.2 ⟨hac.2.1, mem_cls.2 (mem_K_of_path hcb)⟩

lemma conn_inter {g : SimpleGraph (Fin n)} {T : Finset (Fin n)} {i j : Fin n}
    (h : ConnectedIn g T i j) : ConnectedIn g (T ∩ cls g Finset.univ j) i j := by
  obtain ⟨hi, hj, hr⟩ := h
  exact ⟨Finset.mem_inter.2 ⟨hi, mem_cls.2 (mem_K_of_path hr)⟩,
    Finset.mem_inter.2 ⟨hj, self_mem_cls (Finset.mem_univ _)⟩, path_inter hr⟩

lemma cls_inter_eq {g : SimpleGraph (Fin n)} {T : Finset (Fin n)} {j : Fin n} :
    cls g T j = cls g (T ∩ cls g Finset.univ j) j := by
  ext x
  rw [mem_cls, mem_cls]
  exact ⟨conn_inter, connectedIn_mono_set Finset.inter_subset_left⟩

theorem quot_eq_biUnion_core (g : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    quot T g = (quot Finset.univ g).biUnion (fun S => quot (T ∩ S) g) := by
  ext B
  simp only [Finset.mem_biUnion]
  constructor
  · intro hB
    obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
    refine ⟨cls g Finset.univ j, cls_mem_quot (Finset.mem_univ _), ?_⟩
    rw [mem_quot]
    exact ⟨j, Finset.mem_inter.2 ⟨hj, self_mem_cls (Finset.mem_univ _)⟩, cls_inter_eq⟩
  · rintro ⟨S, hS, hB⟩
    obtain ⟨j, hj, rfl⟩ := mem_quot.1 hB
    have hjT := (Finset.mem_inter.1 hj).1
    have hjS := (Finset.mem_inter.1 hj).2
    have hSeq : S = cls g Finset.univ j := quot_eq_cls hS hjS
    subst hSeq
    rw [mem_quot]
    exact ⟨j, hjT, cls_inter_eq.symm⟩

lemma restrict_eq_sum (v : Game n) (g : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    restrict v g X = ∑ T ∈ quot Finset.univ g, uGame v g T X := by
  unfold restrict uGame
  rw [quot_eq_biUnion_core g X, Finset.sum_biUnion]
  intro T hT T' hT' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro B hB hB'
  have h1 := quot_subset hB
  have h2 := quot_subset hB'
  obtain ⟨x, hx⟩ := quot_nonempty hB
  have := quot_disjoint (Finset.mem_coe.1 hT) (Finset.mem_coe.1 hT') hne
  exact Finset.disjoint_left.1 this ((Finset.mem_inter.1 (h1 hx)).2) ((Finset.mem_inter.1 (h2 hx)).2)

lemma shap_uGame_null (v : Game n) (g : SimpleGraph (Fin n)) (T : Finset (Fin n)) (i : Fin n)
    (hi : i ∉ T) : Supermodularity.Cooperative.ShapleyValue (uGame v g T) i = 0 :=
  shap_null _ _ (fun U _ => by simp [uGame, Finset.insert_inter_of_notMem hi])

lemma shap_uGame_sum (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n)) (T : Finset (Fin n)) :
    ∑ i ∈ T, shapley (uGame v g T) i = uGame v g T Finset.univ := by
  have h0 := uGame_empty v g T
  rw [shapley_eq_of_empty _ h0]
  rw [Finset.sum_subset (Finset.subset_univ T)
    (fun i _ hi => shap_uGame_null v g T i hi), shap_efficiency hn, h0, sub_zero]

theorem carrier_identity_core (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S T : Finset (Fin n)) (hS : S ∈ quot Finset.univ g) (hT : T ∈ quot Finset.univ g) :
    ∑ i ∈ S, shapley (uGame v g T) i = if S = T then uGame v g T Finset.univ else 0 := by
  by_cases h : S = T
  · subst h
    rw [if_pos rfl]
    exact shap_uGame_sum hn v g S
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    have hiT : i ∉ T := fun hiT => Finset.disjoint_left.1 (quot_disjoint hS hT h) hi hiT
    rw [shapley_eq_of_empty _ (uGame_empty v g T)]
    exact shap_uGame_null v g T i hiT

theorem shapley_restrict_sum_component_core (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S ∈ quot Finset.univ g) :
    ∑ i ∈ S, shapley (restrict v g) i = ∑ R ∈ quot S g, v R := by
  have key : ∀ i, shapley (restrict v g) i = ∑ T ∈ quot Finset.univ g, shapley (uGame v g T) i := by
    intro i
    rw [shapley_eq_of_empty _ (restrict_empty v g)]
    have : restrict v g = fun X => ∑ T ∈ quot Finset.univ g, uGame v g T X :=
      funext (restrict_eq_sum v g)
    rw [this, shap_sum_fun]
    apply Finset.sum_congr rfl
    intro T _
    rw [shapley_eq_of_empty _ (uGame_empty v g T)]
  simp only [key]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun T hT => carrier_identity_core hn v g S T hS hT)]
  rw [Finset.sum_ite_eq]
  simp [hS, uGame]

lemma shap_two (d : Finset (Fin n) → ℝ) (x y : Fin n) (hd : ∀ U, d U ≠ 0 → x ∈ U ∧ y ∈ U) :
    Supermodularity.Cooperative.ShapleyValue d x =
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => x ∈ U ∧ y ∈ U),
        cc n (U.card - 1) * d U := by
  rw [shap_coeff]
  have h2 : ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => x ∉ U),
      cc n U.card * d U = 0 := by
    apply Finset.sum_eq_zero
    intro U hU
    have : d U = 0 := by
      by_contra hne
      exact (Finset.mem_filter.1 hU).2 (hd U hne).1
    rw [this, mul_zero]
  rw [h2, sub_zero, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro U _
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · simp [hx, hy]
    · have : d U = 0 := by
        by_contra hne
        exact hy (hd U hne).2
      simp [hx, hy, this]
  · simp [hx]

theorem shapley_restrict_isEquitable_core (v : Game n) :
    IsEquitable (fun g => shapley (restrict v g)) := by
  intro g a b hab
  show shapley (restrict v g) a - shapley (restrict v (removeLink g a b)) a =
    shapley (restrict v g) b - shapley (restrict v (removeLink g a b)) b
  set h := removeLink g a b with hh
  have hd : ∀ U : Finset (Fin n), restrict v g U - restrict v h U ≠ 0 → a ∈ U ∧ b ∈ U := by
    intro U hU
    by_contra hc
    apply hU
    have : a ∉ U ∨ b ∉ U := by
      by_contra hc2
      push_neg at hc2
      exact hc hc2
    unfold restrict
    rw [hh, quot_removeLink_of this]
    ring
  rw [shapley_eq_of_empty _ (restrict_empty v g), shapley_eq_of_empty _ (restrict_empty v h)]
  have e1 := shap_sub (restrict v g) (restrict v h) a
  have e2 := shap_sub (restrict v g) (restrict v h) b
  have f1 := shap_two (fun U => restrict v g U - restrict v h U) a b hd
  have f2 := shap_two (fun U => restrict v g U - restrict v h U) b a (fun U hU => (hd U hU).symm)
  have : ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => a ∈ U ∧ b ∈ U),
        cc n (U.card - 1) * (restrict v g U - restrict v h U) =
      ∑ U ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun U => b ∈ U ∧ a ∈ U),
        cc n (U.card - 1) * (restrict v g U - restrict v h U) :=
    Finset.sum_congr (Finset.filter_congr (fun U _ => and_comm)) (fun _ _ => rfl)
  linarith

/-- uniqueness of fair rules -/
theorem fair_unique (v : Game n) (Y1 Y2 : Rule n) (h1 : IsFair v Y1) (h2 : IsFair v Y2) :
    Y1 = Y2 := by
  funext g
  induction g using WellFoundedLT.induction with
  | _ g ih =>
    have hE : ∀ a b, g.Adj a b → Y1 g a - Y2 g a = Y1 g b - Y2 g b := by
      intro a b hab
      have e1 := h1.2 g a b hab
      have e2 := h2.2 g a b hab
      have e3 : Y1 (removeLink g a b) = Y2 (removeLink g a b) := ih _ (removeLink_lt hab)
      rw [e3] at e1
      linarith
    have hconst : ∀ i j, ConnectedIn g Finset.univ i j → Y1 g i - Y2 g i = Y1 g j - Y2 g j := by
      rintro i j ⟨-, -, hr⟩
      induction hr with
      | refl => rfl
      | tail _ hbc ih => exact ih.trans (hE _ _ hbc.2.2)
    funext i
    have hS : cls g Finset.univ i ∈ quot Finset.univ g := cls_mem_quot (Finset.mem_univ i)
    have hsum : ∑ k ∈ cls g Finset.univ i, (Y1 g k - Y2 g k) = 0 := by
      rw [Finset.sum_sub_distrib, h1.1 g _ hS, h2.1 g _ hS, sub_self]
    have hconstS : ∀ k ∈ cls g Finset.univ i, Y1 g k - Y2 g k = Y1 g i - Y2 g i :=
      fun k hk => hconst k i (mem_cls.1 hk)
    rw [Finset.sum_congr rfl hconstS, Finset.sum_const, nsmul_eq_mul] at hsum
    have hpos : ((cls g Finset.univ i).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Finset.card_pos.2 ⟨i, self_mem_cls (Finset.mem_univ i)⟩).ne'
    have := (mul_eq_zero.1 hsum).resolve_left hpos
    linarith

lemma quot_component {g : SimpleGraph (Fin n)} {S : Finset (Fin n)} (hS : S ∈ quot Finset.univ g) :
    quot S g = {S} := by
  obtain ⟨j, _, rfl⟩ := mem_quot.1 hS
  have hall : ∀ y ∈ cls g Finset.univ j, cls g (cls g Finset.univ j) y = cls g Finset.univ j := by
    intro y hy
    have hy' : cls g Finset.univ y = cls g Finset.univ j := cls_eq_of_conn (mem_cls.1 hy)
    ext x
    rw [mem_cls]
    constructor
    · intro h; exact h.1
    · intro hx
      have hxy : ConnectedIn g Finset.univ x y := by
        have h1 := mem_cls.1 hx
        have h2 := mem_cls.1 hy
        exact connectedIn_trans h1 (connectedIn_symm h2)
      have := conn_inter (T := Finset.univ) hxy
      rw [Finset.univ_inter, hy'] at this
      exact this
  ext B
  rw [mem_quot, Finset.mem_singleton]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hall y hy
  · rintro rfl
    exact ⟨j, self_mem_cls (Finset.mem_univ _), (hall j (self_mem_cls (Finset.mem_univ _))).symm⟩

theorem shapley_fair (hn : 0 < n) (v : Game n) : IsFair v (fun g => shapley (restrict v g)) :=
  ⟨fun g S hS => by
    have := shapley_restrict_sum_component_core hn v g S hS
    rw [quot_component hS, Finset.sum_singleton] at this
    exact this,
    shapley_restrict_isEquitable_core v⟩

theorem theorem_1_core (hn : 0 < n) (v : Game n) : ∃! Y : Rule n, IsFair v Y :=
  ⟨_, shapley_fair hn v, fun Y hY => fair_unique v Y _ hY (shapley_fair hn v)⟩

lemma cls_top {S : Finset (Fin n)} {j : Fin n} (hj : j ∈ S) :
    cls (⊤ : SimpleGraph (Fin n)) S j = S := by
  ext x
  rw [mem_cls]
  constructor
  · intro h; exact h.1
  · intro hx
    by_cases hxj : x = j
    · subst hxj; exact connectedIn_refl hx
    · exact ⟨hx, hj, Relation.ReflTransGen.single ⟨hx, hj, by simpa using hxj⟩⟩

lemma quot_top {S : Finset (Fin n)} (hS : S.Nonempty) :
    quot S (⊤ : SimpleGraph (Fin n)) = {S} := by
  ext B
  rw [mem_quot, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact cls_top hj
  · rintro rfl
    obtain ⟨j, hj⟩ := hS
    exact ⟨j, hj, (cls_top hj).symm⟩

theorem theorem_2_core (hn : 0 < n) (v : Game n) (Y : Rule n) (hY : IsFair v Y) :
    (∀ g : SimpleGraph (Fin n), Y g = shapley (restrict v g)) ∧ Y ⊤ = shapley v := by
  have hY' : Y = fun g => shapley (restrict v g) := fair_unique v Y _ hY (shapley_fair hn v)
  subst hY'
  refine ⟨fun g => rfl, ?_⟩
  show shapley (restrict v ⊤) = shapley v
  have : Function.update (restrict v ⊤) ∅ 0 = Function.update v ∅ 0 := by
    funext S
    by_cases hS : S = ∅
    · subst hS; simp
    · rw [Function.update_of_ne hS, Function.update_of_ne hS]
      have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
      simp [restrict, quot_top hne]
  unfold shapley
  rw [this]

theorem shapley_restrict_removeLink_le_core (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) :
    shapley (restrict v (removeLink g a b)) a ≤ shapley (restrict v g) a := by
  rw [shapley_eq_of_empty _ (restrict_empty _ _), shapley_eq_of_empty _ (restrict_empty _ _),
    shapleyValue_def, shapleyValue_def]
  apply Finset.sum_le_sum
  intro S hS
  have haS : a ∉ S := by
    intro h
    have := Finset.mem_powerset.1 hS h
    simp at this
  have hc : 0 ≤ cc n S.card := by unfold cc; positivity
  apply mul_le_mul_of_nonneg_left _ hc
  have h1 := restrict_removeLink_le_core v hv g a b (insert a S) (Finset.insert_nonempty _ _)
  have h2 : restrict v (removeLink g a b) S = restrict v g S := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [restrict_empty]
    · exact (restrict_removeLink_le_core v hv g a b S hne).2 haS
  linarith [h1.1]

theorem theorem_3_core (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v) (Y : Rule n)
    (hY : IsFair v Y) : IsTotallyStable Y := by
  have hY' : Y = fun g => shapley (restrict v g) := fair_unique v Y _ hY (shapley_fair hn v)
  subst hY'
  intro g a b _
  exact shapley_restrict_removeLink_le_core v hv g a b

end Main
end CooperationGraphs.FairRule

open CooperationGraphs.FairRule
open Finset
open scoped Classical

theorem solution {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (hab : g.Adj a b)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    restrict v (removeLink g a b) S ≤ restrict v g S ∧
      (a ∉ S → restrict v (removeLink g a b) S = restrict v g S) := by
  exact restrict_removeLink_le_core v hv g a b S hS
