-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_g_radon_exponential_fourth_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:31:19.373221+00:00
-- url     : https://prove2.me/submissions/3580178a-e297-4d80-901c-2cf72247bd3e

import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A spectrally negative increment of size at least epsilon has a
    uniformly positive fourth exponential weight. -/
theorem solution (ε x : ℝ) (hε : 0 < ε) (hx : x ≤ -ε) :
    (1 - Real.exp (-ε)) ^ 4 ≤ (Real.exp x - 1) ^ 4 := by
  have h_exp : Real.exp x ≤ Real.exp (-ε) :=
    Real.exp_le_exp.mpr hx
  have h_eps : -ε ≤ (0 : ℝ) := by linarith
  have h_exp_one : Real.exp (-ε) ≤ 1 := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr h_eps)
  have h_nonneg : 0 ≤ 1 - Real.exp (-ε) := by linarith
  have h_le : 1 - Real.exp (-ε) ≤ 1 - Real.exp x := by linarith
  calc
    (1 - Real.exp (-ε)) ^ 4 ≤ (1 - Real.exp x) ^ 4 :=
      pow_le_pow_left₀ h_nonneg h_le 4
    _ = (Real.exp x - 1) ^ 4 := by ring
