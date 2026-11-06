-- Prove2me | solution 1 for BianchiIX.normalizedVolumeJacobian_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:16:23.226775+00:00
-- url     : https://prove2.me/submissions/c8d4fade-494e-4d68-ac6c-f9b57c5c090f

import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
import Theorems.Thm_BianchiIX_NormalizedSolution_physical
import Theorems.Thm_BianchiIX_continuousAt_normalizedCorrectedDivergence
import Theorems.Thm_BianchiIX_corrected_divergence_amplitude_pos
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
import Theorems.Thm_BianchiIX_normalizedVolumeJacobian_eq_exp_integral
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

private theorem BianchiIX.normalizedCorrectedDivergence_pos {x : NormalizedState} (hx : positiveWalls x) :
    0 < normalizedCorrectedDivergence x :=
  corrected_divergence_amplitude_pos hx.1 hx.2.1 hx.2.2

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) (htt : t₀ < t) :
    1 < normalizedVolumeJacobian x t₀ t := by
  have hdom := normalizedMaxDomain_contains_Ici hpos hcon t₀
  rw [normalizedVolumeJacobian_eq_exp_integral hpos hcon (hdom htt.le), Real.one_lt_exp_iff]
  have hc : ContinuousOn (fun u => normalizedCorrectedDivergence (normalizedMaxCurve x t₀ u))
      (Icc t₀ t) := by
    intro u hu
    exact ((continuousAt_normalizedCorrectedDivergence
      ((maximalNormalizedSolution x t₀).physical hpos hcon (hdom hu.1)).1).comp
        (hasDerivAt_normalizedMaxCurve (hdom hu.1)).continuousAt).continuousWithinAt
  apply intervalIntegral.integral_pos htt hc
  · intro u hu
    exact (normalizedCorrectedDivergence_pos
      ((maximalNormalizedSolution x t₀).physical hpos hcon (hdom hu.1.le)).1).le
  · exact ⟨t₀, ⟨le_rfl, htt.le⟩, by
      simpa only [normalizedMaxCurve_initial] using normalizedCorrectedDivergence_pos hpos⟩
