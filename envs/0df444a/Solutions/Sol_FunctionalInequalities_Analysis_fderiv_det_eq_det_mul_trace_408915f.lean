-- Prove2me | solution 1 for FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:30:32.899984+00:00
-- url     : https://prove2.me/submissions/7bd726dc-67f8-48a3-99b7-e4c56b78fd8f

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
open scoped Matrix.Norms.Elementwise
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The derivative of the determinant is the sum of row replacements. -/
theorem FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow (M N : Matrix ι ι ℝ) :
    fderiv ℝ Matrix.det M N = ∑ i, (M.updateRow i (N i)).det := by
  change fderiv ℝ (FunctionalInequalities.Analysis.detML : (ι → ι → ℝ) → ℝ) (fun i => M i) (fun i => N i) = _
  rw [(FunctionalInequalities.Analysis.detML.hasFDerivAt (fun i => M i)).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Jacobi's formula**: `D(det)(M)[N] = det M · tr(M⁻¹ N)` for invertible `M` and any direction `N`. -/
theorem solution (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by
  have hNM : (N * M⁻¹) * M = N := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hM, Matrix.mul_one]
  have hrow (i : ι) : N i = ∑ j, (N * M⁻¹) i j • M j := by
    calc
      N i = ((N * M⁻¹) * M) i := congrArg (fun Q : Matrix ι ι ℝ => Q i) hNM.symm
      _ = _ := by
        ext k
        simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [FunctionalInequalities.Analysis.fderiv_det_eq_sum_updateRow]
  calc
    (∑ i, (M.updateRow i (N i)).det) = ∑ i, (N * M⁻¹) i i * M.det := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hrow, Matrix.det_updateRow_sum]
      rfl
    _ = Matrix.trace (N * M⁻¹) * M.det := by
      rw [Matrix.trace, Finset.sum_mul]
      rfl
    _ = M.det * Matrix.trace (M⁻¹ * N) := by
      rw [Matrix.trace_mul_comm]
      ring
