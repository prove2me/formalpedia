-- Prove2me | solution 1 for BianchiIX.hasDerivAt_matrix_det_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:36:55.301977+00:00
-- url     : https://prove2.me/submissions/d7da6c13-3649-4869-919c-7d06391a34af

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
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

private def BianchiIX.determinantMultilinear {n : Type*} [Fintype n] [DecidableEq n] :
    ContinuousMultilinearMap ℝ (fun _ : n => n → ℝ) ℝ :=
  ⟨Matrix.detRowAlternating.toMultilinearMap, continuous_id.matrix_det⟩

/-- Row multilinearity gives Liouville's differential identity, even at singular matrices. -/
theorem solution {n : Type*} [Fintype n] [DecidableEq n]
    {A : ℝ → Matrix n n ℝ} {B : Matrix n n ℝ} {t : ℝ}
    (hA : HasDerivAt A (B * A t) t) :
    HasDerivAt (fun u => (A u).det) (B.trace * (A t).det) t := by
  have H := (determinantMultilinear.hasFDerivAt (A t)).comp_hasDerivAt t hA
  have hrow (i : n) : (B * A t) i = ∑ j, B i j • A t j := by
    ext j
    simp [Matrix.mul_apply]
  have hd : determinantMultilinear.linearDeriv (A t) (B * A t) = B.trace * (A t).det := by
    erw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, (Matrix.updateRow (A t) i ((B * A t) i)).det) = _
    simp_rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
    exact (Finset.sum_mul _ _ _).symm
  exact hd ▸ H
