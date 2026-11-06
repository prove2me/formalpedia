-- Prove2me | solution 1 for BianchiIX.hasDerivAt_normalizedVolumeJacobian
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:10:21.463176+00:00
-- url     : https://prove2.me/submissions/2df88214-fbe1-4423-8cc3-f3b0fe838001

import Definitions.Def_BianchiIX_Dynamics_FlowDeterminant
import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedFlowDeterminant
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedVolumeWeight
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
open scoped Topology

private theorem BianchiIX.normalizedVolumeWeight_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedVolumeWeight x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  exact mul_pos (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2) (by linarith)

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedVolumeJacobian x t₀)
      (normalizedCorrectedDivergence (normalizedMaxCurve x t₀ t) *
        normalizedVolumeJacobian x t₀ t) t := by
  have hp := (maximalNormalizedSolution x t₀).physical hpos hcon ht
  have hW := hasDerivAt_normalizedVolumeWeight (hasDerivAt_normalizedMaxCurve ht) hp.1 hp.2
  have hne := ne_of_gt (normalizedVolumeWeight_pos hp.1)
  apply (((hasDerivAt_normalizedFlowDeterminant ht).const_mul
    (normalizedVolumeWeight x)).div hW hne).congr_deriv
  unfold normalizedVolumeJacobian
  field_simp [hne]
  ring
