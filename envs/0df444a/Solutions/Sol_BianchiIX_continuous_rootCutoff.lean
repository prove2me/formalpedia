-- Prove2me | solution 1 for BianchiIX.continuous_rootCutoff
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:28:52.519198+00:00
-- url     : https://prove2.me/submissions/2469c2a5-bb23-48c0-b8a7-52882f8ba9b2

import Definitions.Def_BianchiIX_Analysis_RootExtension
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


theorem solution : Continuous rootCutoff :=
  (continuous_const.sub continuous_id).max continuous_const
