-- Prove2me | solution 1 for BianchiIX.contDiff_rootPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:38:30.814762+00:00
-- url     : https://prove2.me/submissions/2cb77dc0-0097-4064-a96e-cc6cdad2b348

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_continuous_rootCutoff
import Theorems.Thm_BianchiIX_hasDerivAt_rootPrimitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution : ContDiff ℝ 1 rootPrimitive := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun t => (hasDerivAt_rootPrimitive t).differentiableAt,
    continuous_rootCutoff.congr (fun t => (hasDerivAt_rootPrimitive t).deriv.symm)⟩
