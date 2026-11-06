-- Prove2me | solution 1 for BianchiIX.amplitude_halving_of_small_beta
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:04:43.078351+00:00
-- url     : https://prove2.me/submissions/640464c1-b0c1-4ec6-836a-24859eeb1219

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


theorem solution {B η : ℝ} (hB : 0 ≤ B)
    (hsmall : B ^ η < 1 / 160) : B ^ (η / 3) ≤ 1 / 2 := by
  have hcube : (B ^ (η / 3)) ^ (3 : ℕ) = B ^ η := by
    rw [← Real.rpow_mul_natCast hB]
    congr 1
    norm_num
  by_contra h
  have hle : (1 / 2 : ℝ) ≤ B ^ (η / 3) := (lt_of_not_ge h).le
  have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hle 3
  rw [hcube] at H
  norm_num at H
  linarith
