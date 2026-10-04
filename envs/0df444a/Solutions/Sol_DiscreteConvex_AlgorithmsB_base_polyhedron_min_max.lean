-- Prove2me | solution 1 for DiscreteConvex.AlgorithmsB.base_polyhedron_min_max
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:36:00.449601+00:00
-- url     : https://prove2.me/submissions/5c38475f-4d49-4cef-aafe-1cfabb6fb8d0

import Mathlib
import Definitions.Def_DiscreteConvex_AlgorithmsB_AphiActive
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsConvexCombOfExtremeBases
import Definitions.Def_DiscreteConvex_AlgorithmsB_IsDeltaFeasibleFlow
import Definitions.Def_DiscreteConvex_AlgorithmsB_MinRho
import Definitions.Def_DiscreteConvex_AlgorithmsB_NegPart
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoActiveTriples
import Definitions.Def_DiscreteConvex_AlgorithmsB_NoArcsLeaving
import Definitions.Def_DiscreteConvex_AlgorithmsB_PrecedesIn
import Definitions.Def_DiscreteConvex_AlgorithmsB_Submodular
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppNegR
import Definitions.Def_DiscreteConvex_AlgorithmsB_SuppPosR
import Definitions.Def_DiscreteConvex_AlgorithmsB_ZVec
import Definitions.Def_DiscreteConvex_AlgorithmsB_ExtremeBaseVec
import Definitions.Def_DiscreteConvex_AlgorithmsB_BasePolyhedronR

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open DiscreteConvex.AlgorithmsB

namespace IFFLib

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The elements of `X` whose position in `L` is below `k`. -/
def Xk (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) : Finset V :=
  X.filter (fun v => ((L v : ℕ)) < k)

theorem Xk_succ (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    Xk L X (k + 1) = Xk L X k ∪ X.filter (fun v => ((L v : ℕ)) = k) := by
  ext v; simp only [Xk, Finset.mem_union, Finset.mem_filter]; constructor
  · rintro ⟨h1, h2⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
    · exact Or.inl ⟨h1, h⟩
    · exact Or.inr ⟨h1, h⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩

theorem Xk_disj (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    Disjoint (Xk L X k) (X.filter (fun v => ((L v : ℕ)) = k)) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  simp only [Xk, Finset.mem_filter] at h1 h2
  have := h1.2; have := h2.2; omega

theorem Xk_full (L : V ≃ Fin (Fintype.card V)) (X : Finset V) : Xk L X (Fintype.card V) = X := by
  ext v; simp only [Xk, Finset.mem_filter, and_iff_left_iff_imp]; intro _; exact (L v).isLt

theorem Xk_zero (L : V ≃ Fin (Fintype.card V)) (X : Finset V) : Xk L X 0 = ∅ := by
  ext v; simp [Xk]

/-- At most one element of `X` sits at position `k`. -/
theorem filter_eq_k (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    X.filter (fun v => ((L v : ℕ)) = k) = ∅ ∨
      ∃ v ∈ X, ((L v : ℕ)) = k ∧ X.filter (fun v => ((L v : ℕ)) = k) = {v} := by
  by_cases h : ∃ v ∈ X, ((L v : ℕ)) = k
  · obtain ⟨v, hv, hk⟩ := h
    right
    refine ⟨v, hv, hk, ?_⟩
    ext w; simp only [Finset.mem_filter, Finset.mem_singleton]; constructor
    · rintro ⟨_, hw⟩
      exact L.injective (Fin.ext (by omega))
    · rintro rfl; exact ⟨hv, hk⟩
  · left
    ext w; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hw hk; exact h ⟨w, hw, hk⟩

theorem prefixUpTo_inter (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (v : V) :
    PrefixUpTo L v ∩ X = Xk L X ((L v : ℕ) + 1) := by
  ext w; simp only [PrefixUpTo, Xk, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.le_def]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1⟩

theorem prefixBefore_inter (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (v : V) :
    PrefixBefore L v ∩ X = Xk L X ((L v : ℕ)) := by
  ext w; simp only [PrefixBefore, Xk, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.lt_def]; constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- Telescoping along `L`, restricted to `X`. -/
theorem telescope (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (X : Finset V) (k : ℕ) :
    ∑ v ∈ Xk L X k, (rho (PrefixUpTo L v ∩ X) - rho (PrefixBefore L v ∩ X)) =
      rho (Xk L X k) - rho ∅ := by
  induction k with
  | zero => simp [Xk_zero]
  | succ k ih =>
    rw [Xk_succ, Finset.sum_union (Xk_disj L X k), ih]
    rcases filter_eq_k L X k with h | ⟨v, hv, hk, h⟩
    · rw [h]; simp
    · rw [h, Finset.sum_singleton, prefixUpTo_inter, prefixBefore_inter, hk, Xk_succ, h]
      ring

theorem telescope_full (rho : Finset V → ℤ) (L : V ≃ Fin (Fintype.card V)) (X : Finset V) :
    ∑ v ∈ X, (rho (PrefixUpTo L v ∩ X) - rho (PrefixBefore L v ∩ X)) = rho X - rho ∅ := by
  have := telescope rho L X (Fintype.card V)
  rwa [Xk_full] at this

/-- On a prefix `W` of `L`, the extreme base sums to `ρ(W)`. -/
theorem extreme_prefix (rho : Finset V → ℤ) (hrho : Submodular rho) (L : V ≃ Fin (Fintype.card V))
    (W : Finset V) (hW : ∀ u ∈ W, ∀ w, L w < L u → w ∈ W) :
    ∑ v ∈ W, ExtremeBaseVec rho L v = rho W := by
  have h := telescope_full rho L W
  rw [hrho.1, sub_zero] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  have e1 : PrefixUpTo L v ∩ W = PrefixUpTo L v := by
    ext w; simp only [Finset.mem_inter, PrefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.1
    · intro h; refine ⟨h, ?_⟩
      rcases lt_or_eq_of_le h with h' | h'
      · exact hW v hv w h'
      · rw [L.injective h']; exact hv
  have e2 : PrefixBefore L v ∩ W = PrefixBefore L v := by
    ext w; simp only [Finset.mem_inter, PrefixBefore, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1, fun h => ⟨h, hW v hv w h⟩⟩
  rw [ExtremeBaseVec, e1, e2]

/-- Greedy inequality: the extreme base lies in `B(ρ)`. -/
theorem extreme_le (rho : Finset V → ℤ) (hrho : Submodular rho) (L : V ≃ Fin (Fintype.card V))
    (X : Finset V) : ∑ v ∈ X, ExtremeBaseVec rho L v ≤ rho X := by
  have h := telescope_full rho L X
  rw [hrho.1, sub_zero] at h
  rw [← h]
  refine Finset.sum_le_sum (fun v hv => ?_)
  unfold ExtremeBaseVec
  set A := PrefixBefore L v ∩ X
  set B := PrefixBefore L v
  have hAB : A ⊆ B := Finset.inter_subset_left
  have hvB : v ∉ B := by simp [B, PrefixBefore]
  have e1 : PrefixUpTo L v = insert v B := by
    ext w; simp only [PrefixUpTo, B, PrefixBefore, Finset.mem_insert, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h; rcases lt_or_eq_of_le h with h' | h'
      · right; exact h'
      · left; exact L.injective h'
    · rintro (rfl | h); · exact le_rfl
      · exact le_of_lt h
  have e2 : PrefixUpTo L v ∩ X = insert v A := by
    rw [e1]; ext w; simp only [Finset.mem_inter, Finset.mem_insert, A]; constructor
    · rintro ⟨rfl | h, hx⟩; · left; rfl
      · right; exact ⟨h, hx⟩
    · rintro (rfl | ⟨h, hx⟩); · exact ⟨Or.inl rfl, hv⟩
      · exact ⟨Or.inr h, hx⟩
  rw [e2, e1]
  have hsub := hrho.2 (insert v A) B
  have hu : insert v A ∪ B = insert v B := by
    ext w; simp only [Finset.mem_union, Finset.mem_insert]; constructor
    · rintro ((rfl | h) | h); · left; rfl
      · right; exact hAB h
      · right; exact h
    · rintro (rfl | h); · left; left; rfl
      · right; exact h
  have hi : insert v A ∩ B = A := by
    ext w; simp only [Finset.mem_inter, Finset.mem_insert]; constructor
    · rintro ⟨rfl | h, hb⟩; · exact absurd hb hvB
      · exact h
    · intro h; exact ⟨Or.inr h, hAB h⟩
  rw [hu, hi] at hsub
  linarith

variable {ι : Type*} [DecidableEq ι]

theorem x_sum (rho : Finset V → ℤ) (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V)))
    (lam : ι → ℝ) (x : V → ℝ) (hx : IsConvexCombOfExtremeBases rho I L lam x) (X : Finset V) :
    ∑ v ∈ X, x v = ∑ i ∈ I, lam i * ((∑ v ∈ X, ExtremeBaseVec rho (L i) v : ℤ) : ℝ) := by
  rw [Finset.sum_congr rfl (fun v _ => hx.2.2 v), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  rw [Finset.mul_sum]

/-- `x ∈ B(ρ)`: `x(X) ≤ ρ(X)`. -/
theorem x_le (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) (X : Finset V) :
    ∑ v ∈ X, x v ≤ (rho X : ℝ) := by
  rw [x_sum rho I L lam x hx X]
  calc ∑ i ∈ I, lam i * ((∑ v ∈ X, ExtremeBaseVec rho (L i) v : ℤ) : ℝ)
      ≤ ∑ i ∈ I, lam i * (rho X : ℝ) := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast extreme_le rho hrho (L i) X) (hx.1 i hi))
    _ = (rho X : ℝ) := by rw [← Finset.sum_mul, hx.2.1, one_mul]

/-- On a common prefix, `x(W) = ρ(W)`. -/
theorem x_prefix (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) (W : Finset V)
    (hW : ∀ i ∈ I, ∀ u ∈ W, ∀ w, L i w < L i u → w ∈ W) :
    ∑ v ∈ W, x v = (rho W : ℝ) := by
  rw [x_sum rho I L lam x hx W]
  calc ∑ i ∈ I, lam i * ((∑ v ∈ W, ExtremeBaseVec rho (L i) v : ℤ) : ℝ)
      = ∑ i ∈ I, lam i * (rho W : ℝ) := Finset.sum_congr rfl (fun i hi => by
        rw [extreme_prefix rho hrho (L i) W (hW i hi)])
    _ = (rho W : ℝ) := by rw [← Finset.sum_mul, hx.2.1, one_mul]

/-- `x⁻(V) ≤ x(X)` for every `X`. -/
theorem neg_le (x : V → ℝ) (X : Finset V) : ∑ v, NegPart x v ≤ ∑ v ∈ X, x v := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ X)]
  have h1 : ∑ v ∈ Finset.univ.filter (· ∈ X), NegPart x v ≤ ∑ v ∈ X, x v := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact Finset.sum_le_sum (fun v _ => min_le_right _ _)
  have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬ v ∈ X), NegPart x v ≤ 0 :=
    Finset.sum_nonpos (fun v _ => min_le_left _ _)
  linarith

theorem neg_le_rho (rho : Finset V → ℤ) (hrho : Submodular rho) (I : Finset ι)
    (L : ι → (V ≃ Fin (Fintype.card V))) (lam : ι → ℝ) (x : V → ℝ)
    (hx : IsConvexCombOfExtremeBases rho I L lam x) :
    ∑ v, NegPart x v ≤ (MinRho rho : ℝ) := by
  obtain ⟨X, -, hX⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Finset V)))
    ⟨∅, Finset.mem_univ _⟩ rho
  unfold MinRho; rw [hX]
  exact (neg_le x X).trans (x_le rho hrho I L lam x hx X)

/-- No active triple: `W` is a prefix of every ordering in `I`. -/
theorem prefix_of_no_active (I : Finset ι) (L : ι → (V ≃ Fin (Fintype.card V))) (W : Finset V)
    (h : NoActiveTriples I L W) : ∀ i ∈ I, ∀ u ∈ W, ∀ w, L i w < L i u → w ∈ W := by
  intro i hi
  suffices H : ∀ n : ℕ, ∀ u ∈ W, ((L i u : ℕ)) = n → ∀ w, L i w < L i u → w ∈ W by
    intro u hu w hw; exact H _ u hu rfl w hw
  intro n
  induction n with
  | zero => intro u _ hu w hw; rw [Fin.lt_def] at hw; omega
  | succ n ih =>
    intro u hu hun w hw
    have hn : n < Fintype.card V := by have := (L i u).isLt; omega
    set v := (L i).symm ⟨n, hn⟩ with hv
    have hLv : ((L i v : ℕ)) = n := by simp [v]
    have hvW : v ∈ W := by
      by_contra hvW
      exact h i u v ⟨hi, hu, hvW, by unfold ImmediatePred; omega⟩
    rw [Fin.lt_def] at hw
    rcases lt_or_eq_of_le (show ((L i w : ℕ)) ≤ n by omega) with h' | h'
    · exact ih v hvW hLv w (by rw [Fin.lt_def]; omega)
    · have : w = v := (L i).injective (Fin.ext (by omega))
      rw [this]; exact hvW

end IFFLib

namespace MinMax

open IFFLib

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The lower truncation `ρ'(X) = min_{Y ⊆ X} ρ(Y)`. -/
def low (rho : Finset V → ℤ) (X : Finset V) : ℤ :=
  X.powerset.inf' ⟨∅, Finset.empty_mem_powerset X⟩ rho

/-- The upper envelope `ĝ(X) = min_{Z ⊇ X} g(Z)`. -/
def up (g : Finset V → ℤ) (X : Finset V) : ℤ :=
  (Finset.univ.filter (fun Z => X ⊆ Z)).inf' ⟨Finset.univ, by simp⟩ g

theorem low_le (rho : Finset V → ℤ) (X : Finset V) : low rho X ≤ rho X :=
  Finset.inf'_le _ (Finset.mem_powerset_self X)

theorem low_mono (rho : Finset V → ℤ) {X Y : Finset V} (h : X ⊆ Y) : low rho Y ≤ low rho X :=
  Finset.inf'_mono _ (Finset.powerset_mono.mpr h) _

theorem low_sub (rho : Finset V → ℤ) (hrho : Submodular rho) : Submodular (low rho) := by
  refine ⟨?_, fun A B => ?_⟩
  · simp [low, Finset.powerset_empty, hrho.1]
  · obtain ⟨YA, hYA, eA⟩ := Finset.exists_mem_eq_inf' ⟨∅, Finset.empty_mem_powerset A⟩ rho
    obtain ⟨YB, hYB, eB⟩ := Finset.exists_mem_eq_inf' ⟨∅, Finset.empty_mem_powerset B⟩ rho
    rw [Finset.mem_powerset] at hYA hYB
    have h1 : low rho (A ∪ B) ≤ rho (YA ∪ YB) :=
      Finset.inf'_le _ (Finset.mem_powerset.mpr (Finset.union_subset_union hYA hYB))
    have h2 : low rho (A ∩ B) ≤ rho (YA ∩ YB) :=
      Finset.inf'_le _ (Finset.mem_powerset.mpr (Finset.inter_subset_inter hYA hYB))
    have h3 := hrho.2 YA YB
    show low rho A + low rho B ≥ low rho (A ∪ B) + low rho (A ∩ B)
    unfold low at h1 h2 ⊢
    rw [eA, eB]
    linarith

theorem up_le (g : Finset V → ℤ) (X : Finset V) : up g X ≤ g X :=
  Finset.inf'_le _ (by simp)

theorem up_mono (g : Finset V → ℤ) {X Y : Finset V} (h : X ⊆ Y) : up g X ≤ up g Y :=
  Finset.inf'_mono _ (fun Z hZ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZ ⊢; exact h.trans hZ) _

theorem up_univ (g : Finset V → ℤ) : up g Finset.univ = g Finset.univ := by
  apply le_antisymm (up_le g _)
  refine Finset.le_inf' _ _ (fun Z hZ => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.univ_subset_iff] at hZ
  rw [hZ]

theorem up_sub (g : Finset V → ℤ) (hg : Submodular g) (hpos : ∀ X, 0 ≤ g X) :
    Submodular (up g) := by
  refine ⟨?_, fun A B => ?_⟩
  · apply le_antisymm
    · rw [← hg.1]; exact up_le g ∅
    · obtain ⟨Z, -, eZ⟩ := Finset.exists_mem_eq_inf'
        (s := Finset.univ.filter (fun Z : Finset V => (∅ : Finset V) ⊆ Z)) ⟨Finset.univ, by simp⟩ g
      unfold up; rw [eZ]; exact hpos Z
  · obtain ⟨ZA, hZA, eA⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ.filter (fun Z : Finset V => A ⊆ Z)) ⟨Finset.univ, by simp⟩ g
    obtain ⟨ZB, hZB, eB⟩ := Finset.exists_mem_eq_inf'
      (s := Finset.univ.filter (fun Z : Finset V => B ⊆ Z)) ⟨Finset.univ, by simp⟩ g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hZA hZB
    have m1 : ZA ∪ ZB ∈ Finset.univ.filter (fun Z : Finset V => A ∪ B ⊆ Z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.union_subset_union hZA hZB
    have m2 : ZA ∩ ZB ∈ Finset.univ.filter (fun Z : Finset V => A ∩ B ⊆ Z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.inter_subset_inter hZA hZB
    have h1 : up g (A ∪ B) ≤ g (ZA ∪ ZB) := Finset.inf'_le _ m1
    have h2 : up g (A ∩ B) ≤ g (ZA ∩ ZB) := Finset.inf'_le _ m2
    have h3 := hg.2 ZA ZB
    show up g A + up g B ≥ up g (A ∪ B) + up g (A ∩ B)
    unfold up at h1 h2 ⊢
    rw [eA, eB]
    linarith

theorem prefix_sub (L : V ≃ Fin (Fintype.card V)) (v : V) : PrefixBefore L v ⊆ PrefixUpTo L v := by
  intro w; simp only [PrefixBefore, PrefixUpTo, Finset.mem_filter, Finset.mem_univ, true_and]
  exact le_of_lt

theorem extreme_univ (rho : Finset V → ℤ) (hrho : Submodular rho) (L : V ≃ Fin (Fintype.card V)) :
    ∑ v, ExtremeBaseVec rho L v = rho Finset.univ :=
  extreme_prefix rho hrho L Finset.univ (fun _ _ w _ => Finset.mem_univ w)

end MinMax

open IFFLib MinMax in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (rho : Finset V → ℤ) (hrho : Submodular rho) :
    IsGreatest {t : ℝ | ∃ x : V → ℝ, BasePolyhedronR rho x ∧ t = ∑ v, NegPart x v}
      ((MinRho rho : ℝ)) ∧
    ∃ x : V → ℤ, (∀ X : Finset V, ∑ v ∈ X, (x v : ℝ) ≤ (rho X : ℝ)) ∧
      (∑ v, (x v : ℝ) = (rho Finset.univ : ℝ)) ∧
      (∑ v, NegPart (fun v => (x v : ℝ)) v = (MinRho rho : ℝ)) := by
  classical
  set L := Fintype.equivFin V
  -- the minimum value is attained
  obtain ⟨X0, -, hX0⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset (Finset V)))
    ⟨∅, Finset.mem_univ _⟩ rho
  have hm : MinRho rho = rho X0 := hX0
  -- weak duality
  have weak : ∀ x : V → ℝ, (∀ X : Finset V, ∑ v ∈ X, x v ≤ (rho X : ℝ)) →
      ∑ v, NegPart x v ≤ (MinRho rho : ℝ) := by
    intro x hx
    rw [hm]; exact (neg_le x X0).trans (hx X0)
  -- `y`: greedy base of the lower truncation (all coordinates `≤ 0`)
  have hlow := low_sub rho hrho
  set y : V → ℤ := ExtremeBaseVec (low rho) L with hy
  have y_nonpos : ∀ v, y v ≤ 0 := by
    intro v; simp only [hy, ExtremeBaseVec]; linarith [low_mono rho (prefix_sub L v)]
  have y_le : ∀ X, ∑ v ∈ X, y v ≤ rho X :=
    fun X => (extreme_le (low rho) hlow L X).trans (low_le rho X)
  have y_sum : ∑ v, y v = MinRho rho := by
    rw [hy, extreme_univ (low rho) hlow L]
    apply le_antisymm
    · rw [hm]; exact Finset.inf'_le _ (Finset.mem_powerset.mpr (Finset.subset_univ X0))
    · obtain ⟨Y, -, eY⟩ := Finset.exists_mem_eq_inf'
        ⟨∅, Finset.empty_mem_powerset (Finset.univ : Finset V)⟩ rho
      unfold low; rw [eY]
      exact Finset.inf'_le _ (Finset.mem_univ Y)
  -- `z`: greedy base of the upper envelope of `g = ρ - y` (all coordinates `≥ 0`)
  set g : Finset V → ℤ := fun X => rho X - ∑ v ∈ X, y v with hg
  have g_sub : Submodular g := by
    refine ⟨by simp [hg, hrho.1], fun A B => ?_⟩
    have h := hrho.2 A B
    have hu := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := y)
    simp only [hg]
    linarith
  have g_pos : ∀ X, 0 ≤ g X := fun X => by simp only [hg]; linarith [y_le X]
  have hup := up_sub g g_sub g_pos
  set z : V → ℤ := ExtremeBaseVec (up g) L with hz
  have z_nonneg : ∀ v, 0 ≤ z v := by
    intro v; simp only [hz, ExtremeBaseVec]; linarith [up_mono g (prefix_sub L v)]
  have z_le : ∀ X, ∑ v ∈ X, z v ≤ g X :=
    fun X => (extreme_le (up g) hup L X).trans (up_le g X)
  have z_sum : ∑ v, z v = g Finset.univ := by
    rw [hz, extreme_univ (up g) hup L, up_univ]
  -- `x = y + z`
  set x : V → ℤ := fun v => y v + z v with hx
  have x_le : ∀ X : Finset V, ∑ v ∈ X, (x v : ℝ) ≤ (rho X : ℝ) := by
    intro X
    have := z_le X
    have e : ∑ v ∈ X, x v = ∑ v ∈ X, y v + ∑ v ∈ X, z v := Finset.sum_add_distrib
    have : ∑ v ∈ X, x v ≤ rho X := by simp only [hg] at this; linarith
    exact_mod_cast this
  have x_sum : ∑ v, (x v : ℝ) = (rho Finset.univ : ℝ) := by
    have e : ∑ v, x v = ∑ v, y v + ∑ v, z v := Finset.sum_add_distrib
    have : ∑ v, x v = rho Finset.univ := by rw [e, z_sum]; simp only [hg]; ring
    exact_mod_cast this
  have x_neg : ∑ v, NegPart (fun v => (x v : ℝ)) v = (MinRho rho : ℝ) := by
    apply le_antisymm (weak _ x_le)
    have hterm : ∀ v, ((y v : ℤ) : ℝ) ≤ NegPart (fun v => (x v : ℝ)) v := by
      intro v
      unfold DiscreteConvex.AlgorithmsB.NegPart
      have h1 : ((y v : ℤ) : ℝ) ≤ 0 := by exact_mod_cast y_nonpos v
      have h2 : ((y v : ℤ) : ℝ) ≤ (x v : ℝ) := by
        have : y v ≤ x v := by simp only [hx]; linarith [z_nonneg v]
        exact_mod_cast this
      exact le_min h1 h2
    have := Finset.sum_le_sum (fun v (_ : v ∈ Finset.univ) => hterm v)
    have e : (∑ v, ((y v : ℤ) : ℝ)) = (MinRho rho : ℝ) := by exact_mod_cast y_sum
    linarith
  refine ⟨⟨⟨fun v => (x v : ℝ), ⟨x_le, x_sum⟩, x_neg.symm⟩, ?_⟩, x, x_le, x_sum, x_neg⟩
  rintro t ⟨w, ⟨hw1, -⟩, rfl⟩
  exact weak w hw1

#print axioms solution
