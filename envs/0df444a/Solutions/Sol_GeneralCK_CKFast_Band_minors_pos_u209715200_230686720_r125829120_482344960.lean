-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r125829120_482344960
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-28T16:25:33.905622+00:00
-- url     : https://prove2.me/submissions/53af5e98-0f82-4f7a-9049-9c5ac41711d7

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u209715200_230686720_r125829120_304087040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u209715200_230686720_r304087040_482344960

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/4 : ℝ) (11/40 : ℝ) →
    rho ∈ Set.Icc (3/20 : ℝ) (23/40 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt rho (29/80 : ℝ) with h | h
  · have hr : rho ∈ Set.Icc (3/20 : ℝ) (29/80 : ℝ) := ⟨hr.1, h⟩
    exact GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r125829120_304087040 u rho hu hr hr1
  · have hr : rho ∈ Set.Icc (29/80 : ℝ) (23/40 : ℝ) := ⟨h.le, hr.2⟩
    exact GeneralCK.CKFast.Band.minors_pos_u209715200_230686720_r304087040_482344960 u rho hu hr hr1
