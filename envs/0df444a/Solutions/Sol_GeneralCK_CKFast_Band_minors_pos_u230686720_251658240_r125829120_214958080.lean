-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u230686720_251658240_r125829120_214958080
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T16:20:18.952723+00:00
-- url     : https://prove2.me/submissions/77f396b6-88b7-443e-b52b-675ca1b25aa9

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u230686720_251658240_r125829120_170393600
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u230686720_251658240_r170393600_214958080

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (11/40 : ℝ) (3/10 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (41/160 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt rho (13/64 : ℝ) with h | h
  · have hr : rho ∈ Set.Icc (3/20 : ℝ) (13/64 : ℝ) := ⟨hr.1, h⟩
    exact GeneralCK.CKFast.Band.minors_pos_u230686720_251658240_r125829120_170393600 u rho hu hr hr1
  · have hr : rho ∈ Set.Icc (13/64 : ℝ) (41/160 : ℝ) := ⟨h.le, hr.2⟩
    exact GeneralCK.CKFast.Band.minors_pos_u230686720_251658240_r170393600_214958080 u rho hu hr hr1
