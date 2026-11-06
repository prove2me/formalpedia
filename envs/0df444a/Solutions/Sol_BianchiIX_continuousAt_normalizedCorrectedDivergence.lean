-- Prove2me | solution 1 for BianchiIX.continuousAt_normalizedCorrectedDivergence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:36:57.781789+00:00
-- url     : https://prove2.me/submissions/a5d92d4a-a58f-4fdf-b031-0a29088a07f5

import Definitions.Def_BianchiIX_Dynamics_CorrectedVolume
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


theorem solution {x : NormalizedState}
    (hx : positiveWalls x) : ContinuousAt normalizedCorrectedDivergence x := by
  have hh : 0 ≤ wallAmplitude (x 2) (x 3) (x 4) :=
    Real.rpow_nonneg (mul_pos (mul_pos hx.1 hx.2.1) hx.2.2).le _
  have hc : Continuous (fun z : NormalizedState => wallAmplitude (z 2) (z 3) (z 4)) := by
    unfold wallAmplitude
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp (by fun_prop)
  unfold normalizedCorrectedDivergence correctedDivergence
  exact (continuousAt_const.mul ((show ContinuousAt
    (fun z : NormalizedState => curvature (z 2) (z 3) (z 4)) x by
      unfold curvature; fun_prop).add (continuousAt_const.mul hc.continuousAt))).div
    (continuousAt_const.add (continuousAt_const.mul hc.continuousAt)) (by linarith)
