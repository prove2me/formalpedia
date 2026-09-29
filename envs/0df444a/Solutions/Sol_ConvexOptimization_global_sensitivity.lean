-- Prove2me | solution 1 for ConvexOptimization.global_sensitivity
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-15T03:42:46.585936+00:00
-- url     : https://prove2.me/submissions/55813df7-c2e6-40da-a25b-eb8f2816c0e9

import Mathlib
import Definitions.Def_ConvexOptimization_lagrangeDuality

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n mm p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ)
    (fc : Fin mm → EuclideanSpace ℝ (Fin n) → ℝ)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (hxs : xs ∈ ConvexOptimization.feasibleSet fc a b)
    (lam : Fin mm → ℝ) (hlam : ∀ i, 0 ≤ lam i) (nu : Fin p → ℝ)
    (hzero : ConvexOptimization.dualFunction f₀ fc a b lam nu = (f₀ xs : EReal))
    (u : Fin mm → ℝ) (v : Fin p → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hx_ineq : ∀ i, fc i x ≤ u i)
    (hx_eq : ∀ j, ⟪a j, x⟫ = b j + v j) :
    f₀ xs - ∑ i, lam i * u i - ∑ j, nu j * v j ≤ f₀ x := by
  have hinf : ConvexOptimization.dualFunction f₀ fc a b lam nu ≤
      (ConvexOptimization.lagrangian f₀ fc a b x lam nu : EReal) :=
    iInf_le _ x
  rw [hzero] at hinf
  have hreal : f₀ xs ≤ ConvexOptimization.lagrangian f₀ fc a b x lam nu := by
    exact_mod_cast hinf
  have hi : ∑ i, lam i * fc i x ≤ ∑ i, lam i * u i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx_ineq i) (hlam i)
  have hj : ∑ j, nu j * (⟪a j, x⟫ - b j) = ∑ j, nu j * v j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hx_eq j]
    ring
  simp only [ConvexOptimization.lagrangian] at hreal
  rw [hj] at hreal
  linarith
