-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.SJ_positive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:42.271192+00:00
-- url     : https://prove2.me/submissions/8e1cf399-e07f-47f0-a6b4-07732fe91ec0

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions
import Theorems.Thm_ConsistentSubmodular_LowRollback_child_coefficients

section

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (k q : ℝ) (hk : 4 / 3 ≤ k)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL : 0 < SL k q) : 0 < SJ k q := by
  obtain ⟨hc, ha, ha3, hA⟩ := child_coefficients q hq0 hq1
  have hC : 0 < cpoly q := by linarith
  have hE : 0 < SE q := by unfold SE; linarith
  let v := 9 * cpoly q / SE q
  let T := 4 * SD q * SA q - (SE q) ^ 2
  have hkv : k < v := by
    apply (lt_div_iff₀ hE).mpr
    unfold SL Sbeta SE at *
    nlinarith only [hL]
  have hT : 0 ≤ T := by
    have hi : T = 3119 + 7994 * (1 - q) + 8025 * (1 - q) ^ 2 + 4444 * (1 - q) ^ 3+
        1473 * (1 - q) ^ 4 + 266 * (1 - q) ^ 5 + 23 * (1 - q) ^ 6 := by
      dsimp [T, SD, SA, SE, cpoly, npoly, apoly]
      ring
    have hh : 0 ≤ 1 - q := by linarith
    rw [hi]
    positivity
  have hlower : 0 < SJ (4 / 3) q := by
    have hi : 135 * SJ (4 / 3) q =
        6720 + 27840 * (1 - q) ^ 6 + 128400 * q ^ 2 * (1 - q) ^ 4 + 528840 * q ^ 3 * (1 - q) ^ 3+
        601275 * q ^ 4 * (1 - q) ^ 2 + 263940 * q ^ 5 * (1 - q) + 37260 * q ^ 6 := by
      unfold SJ SE SD SA SB cpoly npoly apoly
      ring
    have hh : 0 ≤ 1 - q := by linarith
    have hp : 0 < 6720 + 27840 * (1 - q) ^ 6 + 128400 * q ^ 2 * (1 - q) ^ 4 + 528840 * q ^ 3 * (1 - q) ^ 3+
        601275 * q ^ 4 * (1 - q) ^ 2 + 263940 * q ^ 5 * (1 - q) + 37260 * q ^ 6 := by positivity
    linarith
  have hupper : 0 < SJ v q := by
    have hp : 0 < 12 - 32 * q + 35 * q ^ 2 - 7 * q ^ 3 := by
      have hx : 0 ≤ 1 - q := by linarith
      have hcub := pow_nonneg hx 3
      have hi : 12 - 32 * q + 35 * q ^ 2 - 7 * q ^ 3 = 14 * (1 - q) ^ 2 - 17 * (1 - q) + 8 + 7 * (1 - q) ^ 3 := by ring
      rw [hi]
      nlinarith [sq_nonneg ((1 - q) - 17 / 28)]
    have hi : (SE q) ^ 2 * SJ v q = 36 * (cpoly q) ^ 3 * (12 - 32 * q + 35 * q ^ 2 - 7 * q ^ 3) := by
      dsimp only [v, SJ]
      field_simp [ne_of_gt hE]
      unfold SE SD SA SB cpoly npoly apoly
      ring
    apply (mul_pos_iff_of_pos_left (sq_pos_of_pos hE)).mp
    rw [hi]
    positivity
  have hid : (v - 4 / 3) * SJ k q = (v - k) * SJ (4 / 3) q + (k - 4 / 3) * SJ v q+
      T * (v - 4 / 3) * (k - 4 / 3) * (v - k) := by dsimp [SJ, T]; ring
  have h1 := mul_pos (sub_pos.mpr hkv) hlower
  have h2 := mul_nonneg (sub_nonneg.mpr hk) hupper.le
  have h3 := mul_nonneg (mul_nonneg (mul_nonneg hT (show 0 ≤ v - 4 / 3 by linarith))
    (sub_nonneg.mpr hk)) (sub_nonneg.mpr hkv.le)
  have hp : 0 < (v - 4 / 3) * SJ k q := by rw [hid]; linarith only [h1, h2, h3]
  exact (mul_pos_iff_of_pos_left (show 0 < v - 4 / 3 by linarith)).mp hp

end
