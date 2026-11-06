-- Prove2me | solution 1 for BianchiIX.trace_normalizedDifferential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:47:07.04111+00:00
-- url     : https://prove2.me/submissions/d73699c9-6c9d-4ee3-b5ca-e7441843466d

import Definitions.Def_BianchiIX_Dynamics_FlowDeterminant
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.hasFDerivAt_normalizedField (x : NormalizedState) :
    HasFDerivAt normalizedField (normalizedDifferential x) x :=
  ((contDiff_normalizedField 1).differentiable (by norm_num) x).hasFDerivAt

end
end

private theorem BianchiIX.normalizedMatrix_apply (A : NormalizedVariation) (i j : Fin 5) :
    normalizedMatrix A i j = A (Pi.single j 1) i := rfl

private theorem BianchiIX.normalizedDifferential_diagonal (x : NormalizedState) (i : Fin 5) :
    normalizedDifferential x (Pi.single i 1) i =
      ![curvature (x 2) (x 3) (x 4), curvature (x 2) (x 3) (x 4),
        rateOne (x 0) (x 1), rateTwo (x 0) (x 1), rateThree (x 0) (x 1)] i := by
  have H := hasDerivAt_pi.mp
    ((hasFDerivAt_normalizedField (Function.update x i (x i))).comp_hasDerivAt (x i)
      (hasDerivAt_update x i (x i))) i
  simp only [Function.update_eq_self] at H
  apply H.unique
  fin_cases i
  · simpa [normalizedField, shearPlus] using
      (((((((hasDerivAt_id (x 0)).const_mul (curvature (x 2) (x 3) (x 4))).sub_const
        (2 * x 2 ^ 2)).add_const (x 3 ^ 2)).add_const (x 4 ^ 2)).add_const (x 2 * x 3)).sub_const
        (2 * x 3 * x 4)).add_const (x 2 * x 4)
  · simpa [normalizedField, shearMinus] using
      ((hasDerivAt_id (x 1)).const_mul (curvature (x 2) (x 3) (x 4))).add_const
        (Real.sqrt 3 * (-x 3 ^ 2 + x 4 ^ 2 + x 2 * x 3 - x 2 * x 4))
  · simpa [normalizedField] using (hasDerivAt_id (x 2)).const_mul (rateOne (x 0) (x 1))
  · simpa [normalizedField] using (hasDerivAt_id (x 3)).const_mul (rateTwo (x 0) (x 1))
  · simpa [normalizedField] using (hasDerivAt_id (x 4)).const_mul (rateThree (x 0) (x 1))

theorem solution (x : NormalizedState) :
    (normalizedMatrix (normalizedDifferential x)).trace = normalizedDivergence x := by
  simp only [Matrix.trace, Matrix.diag, normalizedMatrix_apply, normalizedDifferential_diagonal]
  simp [Fin.sum_univ_succ, normalizedDivergence, rateOne, rateTwo, rateThree]
  ring
