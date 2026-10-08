-- Prove2me | solution 1 for ConvexOptimization.complementary_slackness
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-14T15:17:42.511052+00:00
-- url     : https://prove2.me/submissions/604f0681-9910-4da6-a401-e4ee4d721a81

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory
open ConvexOptimization

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ feasibleSet fc a b)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (hzero : dualFunction f₀ fc a b lam nu = (f₀ xs : EReal)) :
    ∀ i, lam i * fc i xs = 0 := by
  have hobj_le_L : f₀ xs ≤ lagrangian f₀ fc a b xs lam nu := by
    apply EReal.coe_le_coe_iff.mp
    rw [← hzero]
    exact iInf_le _ xs
  have heq : (∑ j, nu j * (⟪a j, xs⟫ - b j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hxs.2 j]
    ring
  have hterm : ∀ i, lam i * fc i xs ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos (hlam i) (hxs.1 i)
  have hsum_nonpos : (∑ i, lam i * fc i xs) ≤ 0 := by
    exact Finset.sum_nonpos fun i _ => hterm i
  have hsum : (∑ i, lam i * fc i xs) = 0 := by
    simp only [lagrangian] at hobj_le_L
    rw [heq] at hobj_le_L
    linarith
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonpos
    (fun k (_hk : k ∈ Finset.univ) => hterm k)).mp hsum i (Finset.mem_univ i)
