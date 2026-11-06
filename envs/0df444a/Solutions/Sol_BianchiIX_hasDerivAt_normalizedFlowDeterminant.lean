-- Prove2me | solution 1 for BianchiIX.hasDerivAt_normalizedFlowDeterminant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:07:07.330398+00:00
-- url     : https://prove2.me/submissions/818f69c7-8417-470e-97c4-0f5e5f26bf1d

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowDeterminant
import Theorems.Thm_BianchiIX_hasDerivAt_matrix_det_of_mul
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedFlowDifferential
import Theorems.Thm_BianchiIX_trace_normalizedDifferential
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

private theorem BianchiIX.normalizedMatrix_apply (A : NormalizedVariation) (i j : Fin 5) :
    normalizedMatrix A i j = A (Pi.single j 1) i := rfl

private theorem BianchiIX.normalizedMatrix_comp (A B : NormalizedVariation) :
    normalizedMatrix (A.comp B) = normalizedMatrix A * normalizedMatrix B :=
  LinearMap.toMatrix'_comp A.toLinearMap B.toLinearMap

private theorem BianchiIX.normalizedMatrix_det (A : NormalizedVariation) :
    (normalizedMatrix A).det = A.det := LinearMap.det_toMatrix' A.toLinearMap

private theorem BianchiIX.hasDerivAt_normalizedMatrix {A : ℝ → NormalizedVariation} {B : NormalizedVariation}
    {t : ℝ} (hA : HasDerivAt A B t) :
    HasDerivAt (fun u => normalizedMatrix (A u)) (normalizedMatrix B) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have H := hasDerivAt_pi.mp (hA.clm_apply (hasDerivAt_const t (Pi.single j (1 : ℝ)))) i
  simpa only [normalizedMatrix_apply, ContinuousLinearMap.map_zero, add_zero] using H

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (fun u => (normalizedFlowDifferential x t₀ u).det)
      (normalizedDivergence (normalizedMaxCurve x t₀ t) *
        (normalizedFlowDifferential x t₀ t).det) t := by
  have H := hasDerivAt_normalizedMatrix (hasDerivAt_normalizedFlowDifferential ht)
  rw [normalizedMatrix_comp] at H
  simpa only [normalizedMatrix_det, trace_normalizedDifferential] using
    hasDerivAt_matrix_det_of_mul H
