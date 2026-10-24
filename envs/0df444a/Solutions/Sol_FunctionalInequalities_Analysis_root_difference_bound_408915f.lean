-- Prove2me | solution 1 for FunctionalInequalities.Analysis.root_difference_bound_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:46:23.348152+00:00
-- url     : https://prove2.me/submissions/e7f252a5-4c1f-4c7e-9f83-d66bcb7688d8

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
section Frobenius
open Matrix Finset
open scoped RealInnerProductSpace
theorem FunctionalInequalities.Analysis.matrixEntries_norm_sq (A : Matrix ι ι ℝ) :
    ‖matrixEntries A‖ ^ 2 = ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  exact Fintype.sum_prod_type _
theorem FunctionalInequalities.Analysis.matrixEntries_inner (A B : Matrix ι ι ℝ) :
    ⟪matrixEntries A, matrixEntries B⟫ = ∑ i, ∑ j, A i j * B i j := by
  rw [PiLp.inner_apply]
  simp only [matrixEntries, PiLp.toLp_apply, Real.inner_apply]
  exact Fintype.sum_prod_type _
end Frobenius
section Sylvester
open Matrix Finset
open scoped RealInnerProductSpace
variable [DecidableEq ι]
omit [DecidableEq ι] in
private theorem FunctionalInequalities.Analysis.left_floor (S D : Matrix ι ι ℝ) {a : ℝ} (hS : QuadraticFloor S a) :
    a * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (S * D) i j := by
  calc
    a * (∑ i, ∑ j, (D i j) ^ 2) = ∑ j, a * (∑ i, (D i j) ^ 2) := by
      rw [Finset.sum_comm, Finset.mul_sum]
    _ ≤ ∑ j, ∑ i, D i j * (S * D) i j := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [QuadraticFloor, dotProduct, mulVec, Matrix.mul_apply] using hS (fun i => D i j)
    _ = ∑ i, ∑ j, D i j * (S * D) i j := Finset.sum_comm
omit [DecidableEq ι] in
private theorem FunctionalInequalities.Analysis.right_floor (T D : Matrix ι ι ℝ) {b : ℝ} (hT : QuadraticFloor T b)
    (hSym : ∀ i j, T i j = T j i) :
    b * (∑ i, ∑ j, (D i j) ^ 2) ≤ ∑ i, ∑ j, D i j * (D * T) i j := by
  have he (i j : ι) : (D * T) i j = (T *ᵥ (fun k => D i k)) j := by
    simp only [Matrix.mul_apply, mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [hSym k j]
    ring
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _hi
  simp_rw [he]
  exact hT (fun j => D i j)
omit [DecidableEq ι] in
/-- **Sylvester coercivity**: `(a + b)‖D‖_F² ≤ ⟪D, SD + DT⟫_F` for floors `a`, `b` and symmetric `T`; no
commutation assumption. -/
theorem FunctionalInequalities.Analysis.sylvester_coercivity (S T D : Matrix ι ι ℝ) {a b : ℝ}
    (hS : QuadraticFloor S a) (hT : QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖matrixEntries D‖ ^ 2 ≤ ⟪matrixEntries D, matrixEntries (S * D + D * T)⟫ := by
  rw [matrixEntries_norm_sq, matrixEntries_inner]
  have hl := left_floor S D hS
  have hr := right_floor T D hT hSym
  calc
    (a + b) * (∑ i, ∑ j, (D i j) ^ 2) =
        a * (∑ i, ∑ j, (D i j) ^ 2) + b * (∑ i, ∑ j, (D i j) ^ 2) := by ring
    _ ≤ (∑ i, ∑ j, D i j * (S * D) i j) + (∑ i, ∑ j, D i j * (D * T) i j) := add_le_add hl hr
    _ = ∑ i, ∑ j, D i j * (S * D + D * T) i j := by
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Root difference bound**: `(a + b)‖S − T‖_F ≤ ‖S² − T²‖_F` from the identity
`S(S − T) + (S − T)T = S² − T²`, which holds without commutation. -/
theorem solution (S T : Matrix ι ι ℝ) {a b : ℝ}
    (hS : FunctionalInequalities.Analysis.QuadraticFloor S a) (hT : FunctionalInequalities.Analysis.QuadraticFloor T b) (hSym : ∀ i j, T i j = T j i) :
    (a + b) * ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ ≤ ‖FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)‖ := by
  have hid : S * (S - T) + (S - T) * T = S * S - T * T := by noncomm_ring
  have hlo := FunctionalInequalities.Analysis.sylvester_coercivity S T (S - T) hS hT hSym
  rw [hid] at hlo
  have hupper : ⟪FunctionalInequalities.Analysis.matrixEntries (S - T), FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)⟫ ≤
      ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ * ‖FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)‖ := by
    have hc : |⟪FunctionalInequalities.Analysis.matrixEntries (S - T), FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)⟫| ≤
        ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ * ‖FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ)
        (FunctionalInequalities.Analysis.matrixEntries (S - T)) (FunctionalInequalities.Analysis.matrixEntries (S * S - T * T))
    exact (le_abs_self _).trans hc
  by_cases hz : ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg _
  have hd : 0 < ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have h := hlo.trans hupper
  have h' : ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ * ((a + b) * ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖) ≤
      ‖FunctionalInequalities.Analysis.matrixEntries (S - T)‖ * ‖FunctionalInequalities.Analysis.matrixEntries (S * S - T * T)‖ := by
    nlinarith only [h]
  exact (mul_le_mul_iff_right₀ hd).mp h'
