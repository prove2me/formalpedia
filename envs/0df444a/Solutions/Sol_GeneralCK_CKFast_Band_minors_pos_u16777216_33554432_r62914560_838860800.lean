-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r62914560_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:24:52.069476+00:00
-- url     : https://prove2.me/submissions/2697acbe-8105-4438-a598-2c0f6b054e25

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_20971520_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_20971520_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_20971520_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_20971520_r87162880_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r159907840_184156160
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r184156160_208404480
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r208404480_256901120
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r256901120_305397760
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_25165824_r305397760_353894400
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r353894400_402391040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r402391040_450887680
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r450887680_499384320
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r499384320_547880960
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r547880960_644874240
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r644874240_741867520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u16777216_33554432_r741867520_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u20971520_25165824_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u20971520_25165824_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u20971520_25165824_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u20971520_25165824_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u20971520_25165824_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_29360128_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_33554432_r159907840_184156160
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_33554432_r184156160_208404480
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_33554432_r208404480_256901120
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_33554432_r256901120_305397760
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u25165824_33554432_r305397760_353894400
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_31457280_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_33554432_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_33554432_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_33554432_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_33554432_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u29360128_33554432_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u31457280_33554432_r62914560_75038720

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/50 : ℝ) (1/25 : ℝ) →
    rho ∈ Set.Icc (3/40 : ℝ) (1 : ℝ) → rho < 1 →
      0 < GeneralCK.Correction.Mleft (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) ∧
      0 < GeneralCK.Correction.Mdet (GeneralCK.H u) (GeneralCK.H (u + rho * (1 / 2 - u))) := by
  intro u rho hu hr hr1
  rcases le_or_gt rho (43/80 : ℝ) with h | h
  · have hr : rho ∈ Set.Icc (3/40 : ℝ) (43/80 : ℝ) := ⟨hr.1, h⟩
    rcases le_or_gt rho (49/160 : ℝ) with h | h
    · have hr : rho ∈ Set.Icc (3/40 : ℝ) (49/160 : ℝ) := ⟨hr.1, h⟩
      rcases le_or_gt rho (61/320 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (3/40 : ℝ) (61/320 : ℝ) := ⟨hr.1, h⟩
        rcases le_or_gt rho (17/128 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (3/40 : ℝ) (17/128 : ℝ) := ⟨hr.1, h⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (133/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (3/40 : ℝ) (133/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (1/40 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r75038720_87162880 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r75038720_87162880 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (1/40 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r87162880_111411200 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r99287040_111411200 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (133/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (3/40 : ℝ) (133/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (7/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r75038720_87162880 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  rcases le_or_gt u (3/80 : ℝ) with h | h
                  · have hu : u ∈ Set.Icc (7/200 : ℝ) (3/80 : ℝ) := ⟨hu.1, h⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u29360128_31457280_r62914560_75038720 u rho hu hr hr1
                  · have hu : u ∈ Set.Icc (3/80 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u31457280_33554432_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r75038720_87162880 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (7/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r99287040_111411200 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r99287040_111411200 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (17/128 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (207/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (1/40 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/50 : ℝ) (1/40 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u16777216_20971520_r111411200_135659520 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (1/40 : ℝ) (3/100 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u20971520_25165824_r111411200_135659520 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r135659520_159907840 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (207/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (7/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r111411200_135659520 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r111411200_135659520 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (7/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (3/100 : ℝ) (7/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u25165824_29360128_r135659520_159907840 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (7/200 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u29360128_33554432_r135659520_159907840 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (61/320 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
        rcases le_or_gt rho (159/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (61/320 : ℝ) (159/640 : ℝ) := ⟨hr.1, h⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (281/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r159907840_184156160 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r184156160_208404480 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (281/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r159907840_184156160 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r184156160_208404480 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (159/640 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r208404480_256901120 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            exact GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r208404480_256901120 u rho hu hr hr1
    · have hr : rho ∈ Set.Icc (49/160 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
      rcases le_or_gt rho (27/64 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (49/160 : ℝ) (27/64 : ℝ) := ⟨hr.1, h⟩
        rcases le_or_gt rho (233/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) := ⟨hr.1, h⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r256901120_305397760 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            exact GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r256901120_305397760 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (3/100 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/50 : ℝ) (3/100 : ℝ) := ⟨hu.1, h⟩
            exact GeneralCK.CKFast.Band.minors_pos_u16777216_25165824_r305397760_353894400 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (3/100 : ℝ) (1/25 : ℝ) := ⟨h.le, hu.2⟩
            exact GeneralCK.CKFast.Band.minors_pos_u25165824_33554432_r305397760_353894400 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (27/64 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
        rcases le_or_gt rho (307/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) := ⟨hr.1, h⟩
          exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r353894400_402391040 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
          exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r402391040_450887680 u rho hu hr hr1
  · have hr : rho ∈ Set.Icc (43/80 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
    rcases le_or_gt rho (123/160 : ℝ) with h | h
    · have hr : rho ∈ Set.Icc (43/80 : ℝ) (123/160 : ℝ) := ⟨hr.1, h⟩
      rcases le_or_gt rho (209/320 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (43/80 : ℝ) (209/320 : ℝ) := ⟨hr.1, h⟩
        rcases le_or_gt rho (381/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) := ⟨hr.1, h⟩
          exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r450887680_499384320 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) := ⟨h.le, hr.2⟩
          exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r499384320_547880960 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (209/320 : ℝ) (123/160 : ℝ) := ⟨h.le, hr.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r547880960_644874240 u rho hu hr hr1
    · have hr : rho ∈ Set.Icc (123/160 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
      rcases le_or_gt rho (283/320 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) := ⟨hr.1, h⟩
        exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r644874240_741867520 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u16777216_33554432_r741867520_838860800 u rho hu hr hr1
