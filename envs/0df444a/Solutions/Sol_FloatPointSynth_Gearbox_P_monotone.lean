-- Prove2me | solution 1 for FloatPointSynth.Gearbox.P_monotone
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:33:21.029683+00:00
-- url     : https://prove2.me/submissions/788cb73e-70ee-415b-9e3a-e46a5189a689

import Mathlib
import Definitions.Def_FloatPointSynth_Gearbox_Cost

open FloatPointSynth.Gearbox in
theorem solution (θ0 : ℝ) (hθ0 : 0 ≤ θ0) (hθ1 : θ0 < Real.pi / 4) (q : ℕ) (hq : 1 ≤ q) :
    FloatPointSynth.Gearbox.P θ0 q ≤ FloatPointSynth.Gearbox.P θ0 (q + 1) ∧
      (0 < θ0 → FloatPointSynth.Gearbox.P θ0 q < FloatPointSynth.Gearbox.P θ0 (q + 1)) := by
  have hg : ∀ x : ℝ, Real.sin (Real.arctan x) ^ 4 + Real.cos (Real.arctan x) ^ 4 =
      (x ^ 4 + 1) / (1 + x ^ 2) ^ 2 := by
    intro x
    have hs : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
    rw [Real.sin_arctan, Real.cos_arctan, div_pow, div_pow, one_pow,
      show Real.sqrt (1 + x ^ 2) ^ 4 = (Real.sqrt (1 + x ^ 2) ^ 2) ^ 2 by ring, hs, ← add_div]
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 ≤ Real.tan θ0 :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two hθ0 (by linarith)
  have ht1 : Real.tan θ0 < 1 := by
    rw [← Real.tan_pi_div_four]
    exact Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith) (by linarith) hθ1
  obtain ⟨x, hx⟩ : ∃ x, x = Real.tan θ0 ^ (2 ^ (q - 1)) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x < 1 := by rw [hx]; exact pow_lt_one₀ ht0 ht1 (by positivity)
  have hnext : Real.tan θ0 ^ (2 ^ (q + 1 - 1)) = x ^ 2 := by
    rw [hx, ← pow_mul, Nat.add_sub_cancel]
    congr 1
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
  unfold FloatPointSynth.Gearbox.P FloatPointSynth.Gearbox.phi
  rw [hg, hg, hnext, ← hx]
  have hd1 : 0 < (1 + x ^ 2) ^ 2 := by positivity
  have hd2 : 0 < (1 + (x ^ 2) ^ 2) ^ 2 := by positivity
  have key : ((x ^ 2) ^ 4 + 1) * (1 + x ^ 2) ^ 2 - (x ^ 4 + 1) * (1 + (x ^ 2) ^ 2) ^ 2 =
      2 * x ^ 2 * (1 - x ^ 2) ^ 2 * (1 + x ^ 2 + x ^ 4) := by ring
  constructor
  · rw [div_le_div_iff₀ hd1 hd2]
    have : 0 ≤ 2 * x ^ 2 * (1 - x ^ 2) ^ 2 * (1 + x ^ 2 + x ^ 4) := by positivity
    linarith
  · intro hθ
    have htp : 0 < Real.tan θ0 := Real.tan_pos_of_pos_of_lt_pi_div_two hθ (by linarith)
    have hxp : 0 < x := by rw [hx]; positivity
    have hx2 : 0 < 1 - x ^ 2 := by nlinarith
    rw [div_lt_div_iff₀ hd1 hd2]
    have : 0 < 2 * x ^ 2 * (1 - x ^ 2) ^ 2 * (1 + x ^ 2 + x ^ 4) := by positivity
    linarith
