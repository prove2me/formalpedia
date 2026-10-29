-- Prove2me | solution 1 for DynamicOnlineLP.DLA.threshold_le_optimal
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T05:52:04.322986+00:00
-- url     : https://prove2.me/submissions/c3dcfbd1-5e9e-4d30-861b-c394a4911acf

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DynamicOnlineLP_DLA_PackingLP
import Theorems.Thm_LP_strong_duality_matrix

open scoped BigOperators
open Matrix DynamicOnlineLP.DLA

private theorem packing_weak_duality {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsFeasible S a d x) (hy : IsDualFeasible S π a p y) :
    primalObj S π x ≤ dualObj S d p y := by
  classical
  calc
    primalObj S π x ≤ ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
    _ = (∑ i, p i * (∑ t ∈ S, a t i * x t)) + ∑ t ∈ S, y t * x t := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ ≤ (∑ i, p i * d i) + ∑ t ∈ S, y t := by
      apply add_le_add
      · exact Finset.sum_le_sum fun i _ ↦
          mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
      · exact Finset.sum_le_sum fun t ht ↦
          (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
    _ = dualObj S d p y := by simp only [dualObj, mul_comm]

private theorem packing_optimal_values_eq {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsPrimalOptimal S π a d x)
    (hy : IsDualOptimal S π a d p y) : primalObj S π x = dualObj S d p y := by
  classical
  let Row := Fin m ⊕ (↥S ⊕ ↥S)
  let A : Matrix Row ↥S ℝ := fun r t ↦ match r with
    | Sum.inl i => a t i
    | Sum.inr (Sum.inl s) => if s = t then 1 else 0
    | Sum.inr (Sum.inr s) => if s = t then -1 else 0
  let b : Row → ℝ
    | Sum.inl i => d i
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 0
  let c : ↥S → ℝ := fun t ↦ π t
  let dual0 : Row → ℝ
    | Sum.inl i => p i
    | Sum.inr (Sum.inl t) => y t
    | Sum.inr (Sum.inr t) => (∑ i, a t i * p i) + y t - π t
  have hP : ∃ u : ↥S → ℝ, A *ᵥ u ≤ b := by
    refine ⟨fun t ↦ x t, ?_⟩
    rintro (i | t | t)
    · change (∑ t : ↥S, a t.val i * x t.val) ≤ d i
      rw [Finset.sum_coe_sort S (fun t ↦ a t i * x t)]
      exact hx.1.1 i
    · simpa [A, b, Matrix.mulVec, dotProduct] using (hx.1.2 t.val t.property).2
    · simpa [A, b, Matrix.mulVec, dotProduct] using
        neg_nonpos.mpr (hx.1.2 t.val t.property).1
  have hD : ∃ v : Row → ℝ, 0 ≤ v ∧ Aᵀ *ᵥ v = c := by
    refine ⟨dual0, ?_, ?_⟩
    · rintro (i | t | t)
      · exact hy.1.1 i
      · exact (hy.1.2 t.val t.property).1
      · exact sub_nonneg.mpr (hy.1.2 t.val t.property).2
    · funext t
      change (∑ r : Row, A r t * dual0 r) = π t
      simp [Row, A, dual0, Fintype.sum_sum_type]
      ring
  obtain ⟨u, v, hu, hv, hvA, heq, _⟩ := LP.strong_duality_matrix A b c hP hD
  let u' : ι → ℝ := fun t ↦ if ht : t ∈ S then u ⟨t, ht⟩ else 0
  let p' : Fin m → ℝ := fun i ↦ v (Sum.inl i)
  let y' : ι → ℝ := fun t ↦ if ht : t ∈ S then v (Sum.inr (Sum.inl ⟨t, ht⟩)) else 0
  have hu' : IsFeasible S a d u' := by
    constructor
    · intro i
      have h := hu (Sum.inl i)
      change (∑ t : ↥S, a t i * u t) ≤ d i at h
      rw [← Finset.sum_coe_sort S (fun t ↦ a t i * u' t)]
      simpa [u'] using h
    · intro t ht
      have hlo := hu (Sum.inr (Sum.inr ⟨t, ht⟩))
      have hhi := hu (Sum.inr (Sum.inl ⟨t, ht⟩))
      constructor
      · have hlo' : -u ⟨t, ht⟩ ≤ 0 := by
          simpa [Matrix.mulVec, dotProduct, A, b] using hlo
        simpa [u', ht] using neg_nonpos.mp hlo'
      · simpa [Matrix.mulVec, dotProduct, A, b, u', ht] using hhi
  have hy' : IsDualFeasible S π a p' y' := by
    refine ⟨fun i ↦ hv (Sum.inl i), ?_⟩
    intro t ht
    refine ⟨by simpa [y', ht] using hv (Sum.inr (Sum.inl ⟨t, ht⟩)), ?_⟩
    have h := congrFun hvA ⟨t, ht⟩
    have hlo := hv (Sum.inr (Sum.inr ⟨t, ht⟩))
    change (0 : ℝ) ≤ v (Sum.inr (Sum.inr ⟨t, ht⟩)) at hlo
    change (∑ r : Row, A r ⟨t, ht⟩ * v r) = π t at h
    simp [Row, A, Fintype.sum_sum_type] at h
    dsimp [p']
    simp only [y', dif_pos ht]
    linarith
  have hprimal : primalObj S π u' = c ⬝ᵥ u := by
    unfold primalObj
    rw [← Finset.sum_coe_sort S (fun t ↦ π t * u' t)]
    simp [dotProduct, c, u']
  have hdual : dualObj S d p' y' = b ⬝ᵥ v := by
    unfold dualObj
    rw [← Finset.sum_coe_sort S y']
    simp [Row, dotProduct, b, p', y', Fintype.sum_sum_type]
  apply le_antisymm
  · exact packing_weak_duality S π a d x p y hx.1 hy.1
  · calc
      dualObj S d p y ≤ dualObj S d p' y' := hy.2 p' y' hy'
      _ = b ⬝ᵥ v := hdual
      _ = c ⬝ᵥ u := heq.symm
      _ = primalObj S π u' := hprimal.symm
      _ ≤ primalObj S π x := hx.2 u' hu'

private theorem packing_complementarity {ι : Type} {m : ℕ} (S : Finset ι)
    (π : ι → ℝ) (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ)
    (p : Fin m → ℝ) (y : ι → ℝ) (hx : IsFeasible S a d x)
    (hy : IsDualFeasible S π a p y) (heq : primalObj S π x = dualObj S d p y) :
    ∀ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t = 0 ∧ y t * (1 - x t) = 0 := by
  classical
  let W := ∑ t ∈ S, ((∑ i, a t i * p i) + y t) * x t
  let R := ∑ i, p i * (∑ t ∈ S, a t i * x t)
  let B := ∑ i, d i * p i
  let Y := ∑ t ∈ S, y t * x t
  let Q := ∑ t ∈ S, y t
  have hW : W = R + Y := by
    dsimp [W, R, Y]
    simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro t ht
    ring
  have hR : R ≤ B := by
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx.1 i) (hy.1 i)
  have hY : Y ≤ Q := Finset.sum_le_sum fun t ht ↦
    (mul_le_mul_of_nonneg_left (hx.2 t ht).2 (hy.2 t ht).1).trans_eq (mul_one _)
  have hfirst : primalObj S π x ≤ W := by
    apply Finset.sum_le_sum
    intro t ht
    exact mul_le_mul_of_nonneg_right (hy.2 t ht).2 (hx.2 t ht).1
  have hWupper : W ≤ B + Y := by rw [hW]; exact add_le_add hR le_rfl
  have hdual : dualObj S d p y = B + Q := rfl
  have heqW : W = dualObj S d p y := by
    apply le_antisymm
    · exact hWupper.trans (add_le_add le_rfl hY)
    · rw [← heq]
      exact hfirst
  have hYeq : Y = Q := by linarith [heqW, hdual, hWupper]
  have hA0 : (∑ t ∈ S, ((∑ i, a t i * p i) + y t - π t) * x t) = 0 := by
    calc
      _ = W - primalObj S π x := by
        dsimp [W, primalObj]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [heqW, heq]; ring
  have hB0 : (∑ t ∈ S, y t * (1 - x t)) = 0 := by
    calc
      _ = Q - Y := by
        dsimp [Q, Y]
        simp_rw [mul_sub, mul_one]
        rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hYeq]; ring
  have hApos (t : ι) (ht : t ∈ S) :
      0 ≤ ((∑ i, a t i * p i) + y t - π t) * x t :=
    mul_nonneg (sub_nonneg.mpr (hy.2 t ht).2) (hx.2 t ht).1
  have hBpos (t : ι) (ht : t ∈ S) : 0 ≤ y t * (1 - x t) :=
    mul_nonneg (hy.2 t ht).1 (sub_nonneg.mpr (hx.2 t ht).2)
  intro t ht
  constructor
  · exact le_antisymm ((Finset.single_le_sum hApos ht).trans_eq hA0) (hApos t ht)
  · exact le_antisymm ((Finset.single_le_sum hBpos ht).trans_eq hB0) (hBpos t ht)

theorem solution {ι : Type} {m : ℕ} (S : Finset ι) (π : ι → ℝ)
    (a : ι → Fin m → ℝ) (d : Fin m → ℝ) (x : ι → ℝ) (p : Fin m → ℝ) (y : ι → ℝ)
    (hx : IsPrimalOptimal S π a d x) (hpy : IsDualOptimal S π a d p y) :
    (∀ t ∈ S, threshold π a p t ≤ x t) ∧
      (GeneralPositionOn S π a → (S.filter (fun t => threshold π a p t ≠ x t)).card ≤ m) := by
  classical
  have heq := packing_optimal_values_eq S π a d x p y hx hpy
  have hcomp := packing_complementarity S π a d x p y hx.1 hpy.1 heq
  have hsum (t : ι) : (∑ i, p i * a t i) = ∑ i, a t i * p i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hthreshold : ∀ t ∈ S, threshold π a p t ≤ x t := by
    intro t ht
    by_cases hπ : π t ≤ ∑ i, p i * a t i
    · simpa [threshold, hπ] using (hx.1.2 t ht).1
    · have hπ' : (∑ i, a t i * p i) < π t := by
        simpa only [hsum t] using lt_of_not_ge hπ
      have hypos : 0 < y t := by linarith [(hpy.1.2 t ht).2]
      have hxone : x t = 1 := by
        rcases mul_eq_zero.mp (hcomp t ht).2 with h | h
        · exact False.elim ((ne_of_gt hypos) h)
        · linarith
      simp [threshold, hπ, hxone]
  refine ⟨hthreshold, ?_⟩
  intro hgp
  apply le_trans (Finset.card_le_card ?_) (hgp p)
  intro t ht
  obtain ⟨htS, hne⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨htS, ?_⟩
  by_contra hnot
  rcases lt_or_gt_of_ne hnot with hlt | hgt
  · have hπ : ¬ π t ≤ ∑ i, p i * a t i := not_le_of_gt hlt
    have hxone : x t = 1 := le_antisymm (hx.1.2 t htS).2
      (by simpa [threshold, hπ] using hthreshold t htS)
    exact hne (by simp [threshold, hπ, hxone])
  · have hπ : π t ≤ ∑ i, p i * a t i := le_of_lt hgt
    have hδpos : 0 < (∑ i, a t i * p i) + y t - π t := by
      rw [hsum t] at hgt
      linarith [(hpy.1.2 t htS).1]
    have hxzero : x t = 0 :=
      (mul_eq_zero.mp (hcomp t htS).1).resolve_left (ne_of_gt hδpos)
    exact hne (by simp [threshold, hπ, hxzero])
