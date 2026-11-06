-- Prove2me | solution 1 for BianchiIX.eraAmplitude_power_series
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:10:37.21926+00:00
-- url     : https://prove2.me/submissions/066d5ede-f82c-4102-87df-97bc3fbc4c36

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_power_halving
import Theorems.Thm_BianchiIX_summable_tsum_le_of_halving
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


theorem solution {B p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1) (hp : 0 ≤ p)
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p := by
  have H := summable_tsum_le_of_halving
    (fun m => Real.rpow_nonneg (eraAmplitude_pos hB (m + k)).le p)
    (fun m => by
      simpa only [Nat.add_right_comm m 1 k] using
        eraAmplitude_power_halving hB hB1 hp hsmall (m + k))
  simpa only [Nat.zero_add] using H
