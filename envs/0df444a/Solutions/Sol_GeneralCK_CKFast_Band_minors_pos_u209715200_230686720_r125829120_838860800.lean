-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r125829120_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T16:44:05.375147+00:00
-- url     : https://prove2.me/submissions/bb98c2fa-78d1-40f5-a989-9b01188469ba

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u209715200_230686720_r125829120_482344960
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u209715200_230686720_r482344960_838860800

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt rho (23/40 : ℝ) with h | h
  · have hr : rho ∈ Set.Icc (3/20 : ℝ) (23/40 : ℝ) := ⟨hr.1, h⟩
    exact GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r125829120_482344960 u rho hu hr hr1
  · have hr : rho ∈ Set.Icc (23/40 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
    exact GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r482344960_838860800 u rho hu hr hr1
