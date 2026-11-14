-- Prove2me | solution 1 for ConsistentSubmodular.middle_three_credits
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:59.807284+00:00
-- url     : https://prove2.me/submissions/7e8c9cd2-37a5-4368-b7e4-86f0fc55f52b

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_MiddleCredits
import Theorems.Thm_ConsistentSubmodular_middle_child_deficit_first
import Theorems.Thm_ConsistentSubmodular_middle_child_deficit_second
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_H
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_Q
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_T
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_G1
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_G2
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_F1
import Theorems.Thm_ConsistentSubmodular_middle_sign_u_F2
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_G1
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_G2
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_F1
import Theorems.Thm_ConsistentSubmodular_middle_sign_z_F2
import Theorems.Thm_ConsistentSubmodular_middle_T_lower

section

namespace ConsistentSubmodular

theorem middle_child_elimination (q d p δ w P : ℝ) (hq4 : q ≤ 4)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P) :
    0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d := by
  have := mul_nonneg (sub_nonneg.mpr hq4) (sub_nonneg.mpr hper)
  rw [hatt] at *
  nlinarith only [this]

theorem middle_child_capacity (q d p δ w P : ℝ) (hq3 : q ≤ 3)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P)
    (hcap : w ≤ 1 - d - δ) :
    0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ := by
  have := mul_nonneg (sub_nonneg.mpr hq3) (sub_nonneg.mpr hcap)
  nlinarith only [this, hatt, hper]

theorem middle_child_credit_combination (q d p δ P : ℝ) (hq : 0 ≤ q) (hq3 : q ≤ 3)
    (hF : 0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d)
    (hC : 0 ≤ q * (2 - 3 * d - P) - 3 * (1 - 4 * d)) :
    0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ := by
  have h1 := mul_nonneg hq hF
  have h2 := mul_nonneg (sub_nonneg.mpr hq3) hC
  nlinarith only [h1, h2]

theorem middle_child_delta_bound (q d p δ : ℝ)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hd : 0 ≤ d) (hpd : d ≤ p)
    (hK : 0 ≤ (3 - q) * (1 - d) - 4 * d - p - 3 * δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : δ ≤ d := by
  have h1 := mul_nonneg (show 0 ≤ 3 - 2 * q by linarith) hK
  have hprod : 0 ≤ (3 - q) * ((5 - q) * d - (3 - q) * δ - (q + 1) * p) := by
    nlinarith only [h1, hJ]
  have hinner := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - q by linarith)
  have h2 := mul_nonneg (show 0 ≤ q + 1 by linarith) (sub_nonneg.mpr hpd)
  have h3 := mul_nonneg (sub_nonneg.mpr hq1) hd
  have hlast : 0 ≤ (3 - q) * (d - δ) := by nlinarith only [hinner, h2, h3]
  have := nonneg_of_mul_nonneg_right hlast (show 0 < 3 - q by linarith)
  linarith

theorem middle_parent_I (k d₀ d p W : ℝ) (hk4 : k ≤ 4)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hper : W + d₀ ≤ p) :
    0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀ := by
  have := mul_nonneg (sub_nonneg.mpr hk4) (sub_nonneg.mpr hper)
  nlinarith only [this, hatt]

theorem middle_parent_cutoff (k d₀ d p : ℝ)
    (_hk : (4 : ℝ) / 3 ≤ k) (_hk2 : k ≤ 2) (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4)
    (hpd : p ≤ 2 * d)
    (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀)
    (hfailed : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀) : (38 : ℝ) / 23 ≤ k := by
  by_cases hk9 : (9 : ℝ) / 5 ≤ k
  · linarith
  have h1 := mul_nonneg (show 0 ≤ 9 - 5 * k by linarith) (sub_nonneg.mpr hpd)
  have hupper : 0 ≤ 4 * k - 6 + (18 - 13 * k) * d := by
    nlinarith only [hI, hfailed, h1]
  by_cases hk18 : k ≤ 18 / 13
  · have h2 := mul_nonneg (show 0 ≤ 18 - 13 * k by linarith) (sub_nonneg.mpr hd4)
    nlinarith
  · have h2 := mul_nonneg (show 0 ≤ 13 * k - 18 by linarith) (sub_nonneg.mpr hd7)
    nlinarith

theorem middle_credit_V (k d₀ d p δ : ℝ)
    (hk : (3 : ℝ) / 2 ≤ k) (hk2 : k ≤ 2) (hd : 0 ≤ d) (hpd : p ≤ 2 * d)
    (hδ : δ ≤ d) (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀) :
    0 ≤ p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀ := by
  have h1 := mul_nonneg (sub_nonneg.mpr hk2) (show 0 ≤ 3 * d - p by linarith)
  have h2 := mul_nonneg (show 0 ≤ 2 * k - 3 by linarith) (sub_nonneg.mpr hδ)
  nlinarith only [hI, h1, h2]

theorem middle_child_benchmark_floor (q d p δ P : ℝ)
    (hq1 : 1 ≤ q) (hq3 : q < 3) (hd : 0 ≤ d) (hp : 0 ≤ p) (hδ : 0 ≤ δ)
    (hF : 0 ≤ (3 - q) * P - (4 - q) * p - q * δ - 4 * d) :
    0 ≤ 2 * P - 3 * p - 4 * d - δ := by
  have hqδ := mul_nonneg (show 0 ≤ q by linarith) hδ
  have hprod : 0 ≤ (3 - q) * (P - p) := by nlinarith only [hF, hqδ, hd, hp]
  have hPp := nonneg_of_mul_nonneg_right hprod (sub_pos.mpr hq3)
  have h1 := mul_nonneg (sub_nonneg.mpr hq1) (show 0 ≤ P - p + δ by linarith)
  nlinarith only [hF, h1]

theorem middle_parent_p_floor (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd7 : (7 : ℝ) / 40 ≤ d) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ (3 - k) * p - k * d - 2 * (4 - k) * d₀) : (49 : ℝ) / 200 ≤ p := by
  have h1 := mul_nonneg (show 0 ≤ 2 * (4 - k) by linarith) hd₀
  have h2 := mul_nonneg (show 0 ≤ k by linarith) (sub_nonneg.mpr hd7)
  have hprod : 0 ≤ (3 - k) * p := by nlinarith only [hI, h1, h2, hk]
  have hp := nonneg_of_mul_nonneg_right hprod (show 0 < 3 - k by linarith)
  have h3 := mul_nonneg (sub_nonneg.mpr hk) hp
  nlinarith

end ConsistentSubmodular

end

section

noncomputable section

namespace ConsistentSubmodular

theorem middle_U_lower (k d₀ d p : ℝ)
    (hk : (38 : ℝ) / 23 ≤ k) (hk7 : k ≤ (7 : ℝ) / 4)
    (hd : (7 : ℝ) / 40 ≤ d) (hp : p ≤ 2 * d) (hI : 0 ≤ middleI k d₀ d p) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hA : 0 ≤ 24 - 3 * k - k ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - k by linarith) (show 0 ≤ 2 + k by linarith)]
  have hH := middle_sign_u_H k hk hk7
  have hQ := middle_sign_u_Q k hk hk7
  have hT := middle_sign_u_T k hk hk7
  have hid : 80 * k * (4 - k) * middleU k d₀ d p =
      40 * (24 - 3 * k - k ^ 2) * middleI k d₀ d p +
      40 * (k ^ 3 + 4 * k ^ 2 - 51 * k + 72) * (2 * d - p) +
      40 * (-k ^ 3 - 19 * k ^ 2 + 134 * k - 144) * (d - 7 / 40) +
      (-7 * k ^ 3 + 187 * k ^ 2 - 822 * k + 912) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < 80 * k * (4 - k) * middleU k d₀ d p := by
    rw [hid]
    have hpd : 0 ≤ 2 * d - p := sub_nonneg.mpr hp
    have hdd : 0 ≤ d - 7 / 40 := sub_nonneg.mpr hd
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 80 * k * (4 - k))).mp hpositive

theorem middle_U_upper_first (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 2 / 25 + 2 * p / 5 ≤ d) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 15 - 7 * k := by linarith
  have hA : 0 ≤ 2 * k ^ 2 - 18 * k + 53 := by nlinarith [sq_nonneg k]
  have hB : 0 < k ^ 2 - k + 3 := by nlinarith [sq_nonneg (k - 1 / 2)]
  have hG := middle_sign_u_G1 k hk hk2
  have hF := middle_sign_u_F1 k hk hk2
  have hid : k * (4 - k) * (15 - 7 * k) * middleU k d₀ d p =
      k * (2 * k ^ 2 - 18 * k + 53) * middleI k d₀ d p +
      5 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 2 / 25 - 2 * p / 5) +
      (4 - k) * (-3 * k ^ 3 - 42 * k ^ 2 + 319 * k - 360) * d₀ +
      (2 / 5 : ℝ) * (4 - k) * (k ^ 3 + 69 * k ^ 2 - 252 * k + 225) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < k * (4 - k) * (15 - 7 * k) * middleU k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 2 / 25 - 2 * p / 5 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < k * (4 - k) * (15 - 7 * k))).mp hpositive

theorem middle_U_upper_second (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 1 / 8 + p / 4 ≤ d) :
    0 < middleU k d₀ d p := by
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 12 - 5 * k := by linarith
  have hA : 0 ≤ k ^ 2 - 12 * k + 40 := by nlinarith [sq_nonneg k]
  have hB : 0 < k ^ 2 - k + 3 := by nlinarith [sq_nonneg (k - 1 / 2)]
  have hG := middle_sign_u_G2 k hk hk2
  have hF := middle_sign_u_F2 k hk hk2
  have hid : k * (4 - k) * (12 - 5 * k) * middleU k d₀ d p =
      k * (k ^ 2 - 12 * k + 40) * middleI k d₀ d p +
      4 * k * (4 - k) * (k ^ 2 - k + 3) * (d - 1 / 8 - p / 4) +
      (4 - k) * (-3 * k ^ 3 - 27 * k ^ 2 + 236 * k - 288) * d₀ +
      (1 / 2 : ℝ) * (4 - k) * (k ^ 3 + 39 * k ^ 2 - 153 * k + 144) := by
    unfold middleU middleCap middleI
    field_simp
    ring
  have hpositive : 0 < k * (4 - k) * (12 - 5 * k) * middleU k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 1 / 8 - p / 4 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < k * (4 - k) * (12 - 5 * k))).mp hpositive

theorem middle_T_upper_first (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 2 / 25 + 2 * p / 5 ≤ d) :
    0 < middleT k d₀ d p := by
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 15 - 7 * k := by linarith
  have hA : 0 ≤ 5 * k ^ 2 - 20 * k + 117 := by nlinarith [sq_nonneg (k - 2)]
  have hB : 0 < 2 * k ^ 2 - 5 * k + 9 := by nlinarith [sq_nonneg (k - 5 / 4)]
  have hG := middle_sign_z_G1 k hk hk2
  have hF := middle_sign_z_F1 k hk hk2
  have hid : (15 - 7 * k) * middleT k d₀ d p =
      (5 * k ^ 2 - 20 * k + 117) * middleI k d₀ d p +
      15 * (4 - k) * (2 * k ^ 2 - 5 * k + 9) * (d - 2 / 25 - 2 * p / 5) +
      (4 - k) * (-14 * k ^ 3 + 33 * k ^ 2 + 164 * k - 171) * d₀ +
      (2 / 5 : ℝ) * (4 - k) * (35 * k ^ 3 - 104 * k ^ 2 + 60 * k + 27) := by
    unfold middleT middleI
    ring
  have hpos : 0 < (15 - 7 * k) * middleT k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 2 / 25 - 2 * p / 5 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem middle_T_upper_second (k d₀ d p : ℝ)
    (hk : (7 : ℝ) / 4 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ middleI k d₀ d p) (hline : 1 / 8 + p / 4 ≤ d) :
    0 < middleT k d₀ d p := by
  have hk4 : 0 < 4 - k := by linarith
  have hden : 0 < 12 - 5 * k := by linarith
  have hA : 0 ≤ k ^ 2 - 4 * k + 72 := by nlinarith [sq_nonneg (k - 2)]
  have hB : 0 < 2 * k ^ 2 - 5 * k + 9 := by nlinarith [sq_nonneg (k - 5 / 4)]
  have hG := middle_sign_z_G2 k hk hk2
  have hF := middle_sign_z_F2 k hk hk2
  have hid : (12 - 5 * k) * middleT k d₀ d p =
      (k ^ 2 - 4 * k + 72) * middleI k d₀ d p +
      12 * (4 - k) * (2 * k ^ 2 - 5 * k + 9) * (d - 1 / 8 - p / 4) +
      (4 - k) * (-10 * k ^ 3 + 21 * k ^ 2 + 139 * k - 180) * d₀ +
      (1 / 2 : ℝ) * (4 - k) * (20 * k ^ 3 - 62 * k ^ 2 + 33 * k + 27) := by
    unfold middleT middleI
    ring
  have hpos : 0 < (12 - 5 * k) * middleT k d₀ d p := by
    rw [hid]
    have hl : 0 ≤ d - 1 / 8 - p / 4 := by linarith
    positivity
  exact (mul_pos_iff_of_pos_left hden).mp hpos

theorem middle_U_positive (k d₀ d p q δ : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 0 < middleU k d₀ d p := by
  have hcut := middle_parent_cutoff k d₀ d p hk hk2 hd7 hd4 hp hI hparent
  by_cases hk7 : k ≤ (7 : ℝ) / 4
  · exact middle_U_lower k d₀ d p hcut hk7 hd7 hp hI
  · have hk7' : (7 : ℝ) / 4 ≤ k := le_of_not_ge hk7
    have hpfloor := middle_parent_p_floor k d₀ d p hk7' hk2 hd7 hd₀ hI
    by_cases hp3 : p ≤ 3 / 10
    · exact middle_U_upper_first k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_first q d p δ hq1 hq4 hδ (by linarith) hp3 hJ)
    · exact middle_U_upper_second k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_second q d p δ hq1 hq4 hδ (le_of_not_ge hp3) (by linarith) hJ)

theorem middle_T_positive (k d₀ d p q δ : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ) : 0 < middleT k d₀ d p := by
  by_cases hk7 : k ≤ (7 : ℝ) / 4
  · exact middle_T_lower k d₀ d p hk hk7 hd₀ hd7 hp hI
  · have hk7' : (7 : ℝ) / 4 ≤ k := le_of_not_ge hk7
    have hpfloor := middle_parent_p_floor k d₀ d p hk7' hk2 hd7 hd₀ hI
    by_cases hp3 : p ≤ 3 / 10
    · exact middle_T_upper_first k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_first q d p δ hq1 hq4 hδ (by linarith) hp3 hJ)
    · exact middle_T_upper_second k d₀ d p hk7' hk2 hd₀ hI
        (middle_child_deficit_second q d p δ hq1 hq4 hδ (le_of_not_ge hp3) (by linarith) hJ)

theorem middle_Z_positive (k d₀ d p q δ P : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hp : p ≤ 2 * d)
    (hI : 0 ≤ middleI k d₀ d p)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hJ : 0 ≤ (36 - 25 * q + 3 * q ^ 2) * d - (3 - q) * (3 - 2 * q) -
      q * (4 - q) * p - q ^ 2 * δ)
    (hLP : 0 ≤ 2 * P - 3 * p - 4 * d - δ)
    (hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) :
    0 < P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ := by
  have hT := middle_T_positive k d₀ d p q δ hk hk2 hd₀ hd7 hd4 hp hI hq1 hq4 hδ hJ
  have hk0 : 0 < k := by linarith
  have hk4 : 0 < 4 - k := by linarith
  have hid : 2 * k * (4 - k) *
      (P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀) =
      middleT k d₀ d p + k * (4 - k) * (2 * P - 3 * p - 4 * d - δ) +
      (1 + 2 * (k - 2) ^ 2) *
        (k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) := by
    unfold middleT
    ring
  have h1 := mul_nonneg (mul_nonneg hk0.le hk4.le) hLP
  have h2 := mul_nonneg (show 0 ≤ 1 + 2 * (k - 2) ^ 2 by positivity) hG
  have hpositive : 0 < 2 * k * (4 - k) *
      (P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀) := by
    linarith only [hid, hT, h1, h2]
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * k * (4 - k))).mp hpositive

end ConsistentSubmodular

end

end

section

open ConsistentSubmodular

theorem solution (k d₀ d p W q δ w P : ℝ)
    (hk : (4 : ℝ) / 3 ≤ k) (hk2 : k ≤ 2) (hd₀ : 0 ≤ d₀)
    (hd7 : (7 : ℝ) / 40 ≤ d) (hd4 : d ≤ 1 / 4) (hpd : d ≤ p) (hp : p ≤ 2 * d)
    (hparentatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hparentper : W + d₀ ≤ p)
    (hparent : k * p ≤ 2 * k - 3 + 3 * (4 - k) * d₀)
    (hq1 : 1 ≤ q) (hq4 : q ≤ (4 : ℝ) / 3) (hδ : 0 ≤ δ)
    (hatt : P = (4 - q) * w - q * δ - 4 * d) (hper : p + w ≤ P)
    (hcap : w ≤ 1 - d - δ) (hfailed : 0 ≤ q * (2 - 3 * d - P) - 3 * (1 - 4 * d))
    (hG : 0 ≤ k * (4 - k) * δ - p - (k - 2) ^ 2 * d + (4 - k) * (3 - k) * d₀) :
    0 < d - 2 * middleCap k d₀ + 3 * p - (3 - k) * W ∧
    0 ≤ p + (3 - 2 * k) * (d + δ) - 2 * (4 - k) * d₀ ∧
    0 < P - (k - 1) + (k - 2) ^ 2 * (d + δ) - (4 - k) ^ 2 * d₀ := by
  have hI := middle_parent_I k d₀ d p W (by linarith) hparentatt hparentper
  have hF := middle_child_elimination q d p δ w P (by linarith) hatt hper
  have hK := middle_child_capacity q d p δ w P (by linarith) hatt hper hcap
  have hJ := middle_child_credit_combination q d p δ P (by linarith) (by linarith) hF hfailed
  have hδd := middle_child_delta_bound q d p δ hq1 hq4 (by linarith) hpd hK hJ
  have hcut := middle_parent_cutoff k d₀ d p hk hk2 hd7 hd4 hp hI hparent
  have hLP := middle_child_benchmark_floor q d p δ P hq1 (by linarith) (by linarith)
    (by linarith) hδ hF
  have hU := middle_U_positive k d₀ d p q δ hk hk2 hd₀ hd7 hd4 hp hI hparent hq1 hq4 hδ hJ
  have hW : W = (p + k * d + (4 - k) * d₀) / (4 - k) := by
    apply (eq_div_iff (show 4 - k ≠ 0 by linarith)).2
    nlinarith only [hparentatt]
  refine ⟨?_, middle_credit_V k d₀ d p δ (by linarith) hk2 (by linarith) hp hδd hI,
    middle_Z_positive k d₀ d p q δ P hk hk2 hd₀ hd7 hd4 hp hI hq1 hq4 hδ hJ hLP hG⟩
  rw [hW]
  exact hU

end
