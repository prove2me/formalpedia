-- Prove2me | solution 1 for BianchiIX.rootExtension_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:45:05.681235+00:00
-- url     : https://prove2.me/submissions/2dbed7c9-8815-4beb-81e9-93adab5c592a

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootExtension_error
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


theorem solution {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) :
    (1 - θ / 4) * s ≤ rootExtension s d e x ∧
      rootExtension s d e x ≤ (1 + θ / 4) * s := by
  have h := abs_le.mp (rootExtension_error hs he hx hd)
  constructor <;> nlinarith [h.1, h.2]
