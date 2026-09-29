-- Prove2me | solution 1 for GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r62914560_838860800
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-09-27T11:26:29.947439+00:00
-- url     : https://prove2.me/submissions/e262055e-126b-441b-9d9d-75546a8676c1

import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_35651584_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_37748736_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_37748736_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_37748736_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_37748736_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_37748736_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r159907840_184156160
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r184156160_208404480
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r208404480_232652800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r232652800_256901120
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r256901120_305397760
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_41943040_r305397760_353894400
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r353894400_402391040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r402391040_450887680
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r450887680_499384320
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r499384320_547880960
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r547880960_644874240
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r644874240_741867520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u33554432_50331648_r741867520_838860800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u35651584_37748736_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_39845888_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_41943040_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_41943040_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_41943040_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_41943040_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u37748736_41943040_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u39845888_41943040_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_44040192_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_46137344_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_46137344_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_46137344_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_46137344_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_46137344_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r159907840_184156160
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r184156160_208404480
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r208404480_232652800
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r232652800_256901120
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r256901120_305397760
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u41943040_50331648_r305397760_353894400
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u44040192_46137344_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_48234496_r62914560_75038720
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_50331648_r111411200_135659520
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_50331648_r135659520_159907840
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_50331648_r75038720_87162880
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_50331648_r87162880_99287040
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u46137344_50331648_r99287040_111411200
import Theorems.Thm_GeneralCK_CKFast_Band_minors_pos_u48234496_50331648_r62914560_75038720

theorem solution : ∀ u rho : ℝ, u ∈ Set.Icc (1/25 : ℝ) (3/50 : ℝ) →
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
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (133/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (3/40 : ℝ) (133/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (9/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  rcases le_or_gt u (17/400 : ℝ) with h | h
                  · have hu : u ∈ Set.Icc (1/25 : ℝ) (17/400 : ℝ) := ⟨hu.1, h⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u33554432_35651584_r62914560_75038720 u rho hu hr hr1
                  · have hu : u ∈ Set.Icc (17/400 : ℝ) (9/200 : ℝ) := ⟨h.le, hu.2⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u35651584_37748736_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r75038720_87162880 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  rcases le_or_gt u (19/400 : ℝ) with h | h
                  · have hu : u ∈ Set.Icc (9/200 : ℝ) (19/400 : ℝ) := ⟨hu.1, h⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u37748736_39845888_r62914560_75038720 u rho hu hr hr1
                  · have hu : u ∈ Set.Icc (19/400 : ℝ) (1/20 : ℝ) := ⟨h.le, hu.2⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u39845888_41943040_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r75038720_87162880 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (9/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r99287040_111411200 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r99287040_111411200 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (133/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (3/40 : ℝ) (133/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (11/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  rcases le_or_gt u (21/400 : ℝ) with h | h
                  · have hu : u ∈ Set.Icc (1/20 : ℝ) (21/400 : ℝ) := ⟨hu.1, h⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u41943040_44040192_r62914560_75038720 u rho hu hr hr1
                  · have hu : u ∈ Set.Icc (21/400 : ℝ) (11/200 : ℝ) := ⟨h.le, hu.2⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u44040192_46137344_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r75038720_87162880 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (229/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (3/40 : ℝ) (229/2560 : ℝ) := ⟨hr.1, h⟩
                  rcases le_or_gt u (23/400 : ℝ) with h | h
                  · have hu : u ∈ Set.Icc (11/200 : ℝ) (23/400 : ℝ) := ⟨hu.1, h⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u46137344_48234496_r62914560_75038720 u rho hu hr hr1
                  · have hu : u ∈ Set.Icc (23/400 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
                    exact GeneralCK.CKFast.Band.minors_pos_u48234496_50331648_r62914560_75038720 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (229/2560 : ℝ) (133/1280 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r75038720_87162880 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (11/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) := ⟨hu.1, h⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r99287040_111411200 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
                rcases le_or_gt rho (303/2560 : ℝ) with h | h
                · have hr : rho ∈ Set.Icc (133/1280 : ℝ) (303/2560 : ℝ) := ⟨hr.1, h⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r87162880_99287040 u rho hu hr hr1
                · have hr : rho ∈ Set.Icc (303/2560 : ℝ) (17/128 : ℝ) := ⟨h.le, hr.2⟩
                  exact GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r99287040_111411200 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (17/128 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (207/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (9/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r111411200_135659520 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r111411200_135659520 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (9/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/25 : ℝ) (9/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u33554432_37748736_r135659520_159907840 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (9/200 : ℝ) (1/20 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u37748736_41943040_r135659520_159907840 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (207/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (17/128 : ℝ) (207/1280 : ℝ) := ⟨hr.1, h⟩
              rcases le_or_gt u (11/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r111411200_135659520 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r111411200_135659520 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (207/1280 : ℝ) (61/320 : ℝ) := ⟨h.le, hr.2⟩
              rcases le_or_gt u (11/200 : ℝ) with h | h
              · have hu : u ∈ Set.Icc (1/20 : ℝ) (11/200 : ℝ) := ⟨hu.1, h⟩
                exact GeneralCK.CKFast.Band.minors_pos_u41943040_46137344_r135659520_159907840 u rho hu hr hr1
              · have hu : u ∈ Set.Icc (11/200 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
                exact GeneralCK.CKFast.Band.minors_pos_u46137344_50331648_r135659520_159907840 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (61/320 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
        rcases le_or_gt rho (159/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (61/320 : ℝ) (159/640 : ℝ) := ⟨hr.1, h⟩
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (281/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r159907840_184156160 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r184156160_208404480 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (281/1280 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (61/320 : ℝ) (281/1280 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r159907840_184156160 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (281/1280 : ℝ) (159/640 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r184156160_208404480 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (159/640 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            rcases le_or_gt rho (71/256 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r208404480_232652800 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r232652800_256901120 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            rcases le_or_gt rho (71/256 : ℝ) with h | h
            · have hr : rho ∈ Set.Icc (159/640 : ℝ) (71/256 : ℝ) := ⟨hr.1, h⟩
              exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r208404480_232652800 u rho hu hr hr1
            · have hr : rho ∈ Set.Icc (71/256 : ℝ) (49/160 : ℝ) := ⟨h.le, hr.2⟩
              exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r232652800_256901120 u rho hu hr hr1
    · have hr : rho ∈ Set.Icc (49/160 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
      rcases le_or_gt rho (27/64 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (49/160 : ℝ) (27/64 : ℝ) := ⟨hr.1, h⟩
        rcases le_or_gt rho (233/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (49/160 : ℝ) (233/640 : ℝ) := ⟨hr.1, h⟩
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r256901120_305397760 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r256901120_305397760 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (233/640 : ℝ) (27/64 : ℝ) := ⟨h.le, hr.2⟩
          rcases le_or_gt u (1/20 : ℝ) with h | h
          · have hu : u ∈ Set.Icc (1/25 : ℝ) (1/20 : ℝ) := ⟨hu.1, h⟩
            exact GeneralCK.CKFast.Band.minors_pos_u33554432_41943040_r305397760_353894400 u rho hu hr hr1
          · have hu : u ∈ Set.Icc (1/20 : ℝ) (3/50 : ℝ) := ⟨h.le, hu.2⟩
            exact GeneralCK.CKFast.Band.minors_pos_u41943040_50331648_r305397760_353894400 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (27/64 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
        rcases le_or_gt rho (307/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (27/64 : ℝ) (307/640 : ℝ) := ⟨hr.1, h⟩
          exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r353894400_402391040 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (307/640 : ℝ) (43/80 : ℝ) := ⟨h.le, hr.2⟩
          exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r402391040_450887680 u rho hu hr hr1
  · have hr : rho ∈ Set.Icc (43/80 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
    rcases le_or_gt rho (123/160 : ℝ) with h | h
    · have hr : rho ∈ Set.Icc (43/80 : ℝ) (123/160 : ℝ) := ⟨hr.1, h⟩
      rcases le_or_gt rho (209/320 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (43/80 : ℝ) (209/320 : ℝ) := ⟨hr.1, h⟩
        rcases le_or_gt rho (381/640 : ℝ) with h | h
        · have hr : rho ∈ Set.Icc (43/80 : ℝ) (381/640 : ℝ) := ⟨hr.1, h⟩
          exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r450887680_499384320 u rho hu hr hr1
        · have hr : rho ∈ Set.Icc (381/640 : ℝ) (209/320 : ℝ) := ⟨h.le, hr.2⟩
          exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r499384320_547880960 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (209/320 : ℝ) (123/160 : ℝ) := ⟨h.le, hr.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r547880960_644874240 u rho hu hr hr1
    · have hr : rho ∈ Set.Icc (123/160 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
      rcases le_or_gt rho (283/320 : ℝ) with h | h
      · have hr : rho ∈ Set.Icc (123/160 : ℝ) (283/320 : ℝ) := ⟨hr.1, h⟩
        exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r644874240_741867520 u rho hu hr hr1
      · have hr : rho ∈ Set.Icc (283/320 : ℝ) (1 : ℝ) := ⟨h.le, hr.2⟩
        exact GeneralCK.CKFast.Band.minors_pos_u33554432_50331648_r741867520_838860800 u rho hu hr hr1
