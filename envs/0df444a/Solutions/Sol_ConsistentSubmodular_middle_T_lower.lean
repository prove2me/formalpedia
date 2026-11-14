-- Prove2me | solution 1 for ConsistentSubmodular.middle_T_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:30.741506+00:00
-- url     : https://prove2.me/submissions/4773b690-86dc-4bc3-ab87-e3805b425a64

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_Nplus
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_Nminus

section

open ConsistentSubmodular

theorem solution (k d₀ d p : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk7 : k ≤ (7 : ℝ) / 4) (hd₀ : 0 ≤ d₀)
    (hd : (7 : ℝ) / 40 ≤ d) (hp : p ≤ 2 * d) (hI : 0 ≤ middleI k d₀ d p) :
    0 < middleT k d₀ d p := by
  let Q := 27 - k - 2 * k ^ 2
  let H := 2 * k ^ 3 - 3 * k ^ 2 - 38 * k + 63
  let D := -2 * k ^ 3 + 9 * k ^ 2 - 13 * k + 72
  have hk0 : 0 < k := by linarith
  have hk3 : 0 < 3 - k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hk1 : 0 ≤ k - 1 := by linarith
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    nlinarith [mul_nonneg (show 0 ≤ 2 - k by linarith) (show 0 ≤ 2 + k by linarith)]
  have hNp := middle_sign_z_Nplus k hk hk7
  have hNm := middle_sign_z_Nminus k hk hk7
  have hproduct : 0 ≤ 160 * k * (4 - k) * (k - 1) := by positivity
  have hD2H : 0 < D - 2 * H := by
    dsimp [D, H]
    nlinarith only [hNp, hproduct]
  have hE : 0 < (3 - k) * D - k * H := by
    have hprod := mul_nonneg hk3.le hproduct
    dsimp [D, H]
    nlinarith only [hNm, hprod]
  have hdd : 0 ≤ d - 7 / 40 := sub_nonneg.mpr hd
  by_cases hH : 0 ≤ H
  · have hid : 2 * middleT k d₀ d p =
        Q * middleI k d₀ d p + H * (2 * d - p) + (D - 2 * H) * (d - 7 / 40) +
          (118 * k ^ 3 - 695 * k ^ 2 + 1081 * k - 378) / 40 := by
      dsimp [Q, H, D, middleI, middleT]
      ring
    have hpos : 0 < 2 * middleT k d₀ d p := by
      rw [hid]
      have hpd : 0 ≤ 2 * d - p := sub_nonneg.mpr hp
      positivity
    linarith
  · have hparent : 0 ≤ (3 - k) * p - k * d := by
      have := mul_nonneg (show 0 ≤ 2 * (4 - k) by linarith) hd₀
      unfold middleI at hI
      nlinarith
    have hid : 2 * (3 - k) * middleT k d₀ d p =
        (3 - k) * Q * middleI k d₀ d p - H * ((3 - k) * p - k * d) +
          ((3 - k) * D - k * H) * (d - 7 / 40) +
          (-160 * k ^ 4 + 1196 * k ^ 3 - 2494 * k ^ 2 + 702 * k + 1512) / 40 := by
      dsimp [Q, H, D, middleI, middleT]
      ring
    have hpos : 0 < 2 * (3 - k) * middleT k d₀ d p := by
      rw [hid]
      have hnegative : 0 ≤ -H := by linarith
      have hprod := mul_nonneg hnegative hparent
      have hfirst := mul_nonneg (mul_nonneg hk3.le hQ) hI
      have hthird := mul_nonneg hE.le hdd
      linarith
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * (3 - k))).mp hpos

end
