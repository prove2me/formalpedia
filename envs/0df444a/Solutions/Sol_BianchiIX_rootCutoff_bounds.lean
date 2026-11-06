-- Prove2me | solution 1 for BianchiIX.rootCutoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:28:55.657267+00:00
-- url     : https://prove2.me/submissions/5d30a731-f3c4-4cbd-894b-9a795da78fa4

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


theorem solution {t : ℝ} (ht : 0 ≤ t) : 0 ≤ rootCutoff t ∧ rootCutoff t ≤ 1 :=
  ⟨le_max_right _ _, max_le (by linarith) zero_le_one⟩
