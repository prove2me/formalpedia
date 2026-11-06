-- Prove2me | solution 1 for BianchiIX.eraAmplitude_series_of_small_beta
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:12:34.739475+00:00
-- url     : https://prove2.me/submissions/9ab1a7fd-010d-4d1c-9a77-dcf133f74e13

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Theorems.Thm_BianchiIX_amplitude_halving_of_small_beta
import Theorems.Thm_BianchiIX_amplitude_power_budget
import Theorems.Thm_BianchiIX_eraAmplitude_power_series
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open BianchiIX
open Filter
open scoped Topology


theorem solution {B η p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηp : η ≤ p) (hsmall : B ^ η < 1 / 160) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p :=
  eraAmplitude_power_series hB hB1 (hη.trans hηp)
    (amplitude_power_budget hB le_rfl hB1 hη hηp (amplitude_halving_of_small_beta hB.le hsmall)) k
