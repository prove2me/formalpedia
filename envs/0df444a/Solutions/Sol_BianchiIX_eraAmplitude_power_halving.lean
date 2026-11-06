-- Prove2me | solution 1 for BianchiIX.eraAmplitude_power_halving
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:08:58.287565+00:00
-- url     : https://prove2.me/submissions/6cfce3c8-debb-46b3-9a55-26268f2161e3

import Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
import Theorems.Thm_BianchiIX_eraAmplitude_le
import Theorems.Thm_BianchiIX_eraAmplitude_pos
import Theorems.Thm_BianchiIX_eraAmplitude_power_succ
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
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p ≤ (1 / 2) * eraAmplitude B m ^ p := by
  rw [eraAmplitude_power_succ hB]
  have hfactor : eraAmplitude B m ^ (p / 3) ≤ 1 / 2 :=
    (Real.rpow_le_rpow (eraAmplitude_pos hB m).le (eraAmplitude_le hB.le hB1 m)
      (by positivity)).trans hsmall
  nlinarith [mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg (eraAmplitude_pos hB m).le p)]
