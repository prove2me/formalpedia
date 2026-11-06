-- Prove2me | solution 1 for BianchiIX.amplitude_power_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:04:18.32341+00:00
-- url     : https://prove2.me/submissions/619dd0f3-61c0-4eb9-bac5-eb302dab6f2d

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


theorem solution {B Bmax η p : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hmax1 : Bmax ≤ 1) (hη : 0 ≤ η) (hηp : η ≤ p)
    (hsmall : Bmax ^ (η / 3) ≤ 1 / 2) : B ^ (p / 3) ≤ 1 / 2 := by
  exact ((Real.rpow_le_rpow_of_exponent_ge hB (hmax.trans hmax1)
    (by linarith : η / 3 ≤ p / 3)).trans
      (Real.rpow_le_rpow hB.le hmax (by positivity))).trans hsmall
