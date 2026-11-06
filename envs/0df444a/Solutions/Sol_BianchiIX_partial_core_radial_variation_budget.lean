-- Prove2me | solution 1 for BianchiIX.partial_core_radial_variation_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:55:01.380825+00:00
-- url     : https://prove2.me/submissions/34316374-7d2f-4c9f-b485-9e57ddab7359

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


theorem solution {r K k U P dR dU dP dz : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hk : 0 < k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (_hU : 0 ≤ U) (hKU : k * U ≤ 1) (hP : 0 ≤ P ∧ P ≤ 1)
    (hR : |dR| ≤ K / r ^ 2) (hdU : |dU| ≤ K * U / r)
    (hdP : |dP| ≤ K * P / r) (hdz : |dz| ≤ K / r) :
    |dR| + k * |dU| + |dP| + (k ^ 2 * U + P / k) * |dz| ≤ 5 * K ^ 2 / r ^ 2 := by
  have hr0 := hr.1
  have hP0 := hP.1
  have hP1 := hP.2
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hscale : K / r ≤ K ^ 2 / r ^ 2 := by
    apply (div_le_div_iff₀ hr.1 (sq_pos_of_pos hr.1)).mpr
    have H := mul_le_mul_of_nonneg_left hr.2 hK0
    nlinarith only [mul_le_mul_of_nonneg_right H hr.1.le,
      mul_le_mul_of_nonneg_right hKK hr.1.le]
  have hplain : K ^ 2 ≤ K ^ 2 / r ^ 2 := le_div_self (sq_nonneg K) (sq_pos_of_pos hr.1)
    (by nlinarith only [hr.1, hr.2])
  have HR := hR.trans (div_le_div_of_nonneg_right hKK (sq_nonneg r))
  have HU : k * |dU| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ ≤ k * (K * U / r) := mul_le_mul_of_nonneg_left hdU hk.le
      _ = (K / r) * (k * U) := by ring
      _ ≤ K / r := mul_le_of_le_one_right (by positivity) hKU
      _ ≤ _ := hscale
  have HP : |dP| ≤ K ^ 2 / r ^ 2 := hdP.trans (le_trans
    (div_le_div_of_nonneg_right (mul_le_of_le_one_right hK0 hP.2) hr.1.le) hscale)
  have HZ : k ^ 2 * U * |dz| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ = (k * U) * k * |dz| := by ring
      _ ≤ 1 * (K / r) * (K / r) := by gcongr
      _ = _ := by ring
  have HW : P / k * |dz| ≤ K ^ 2 / r ^ 2 := by
    calc
      _ = P * (1 / k) * |dz| := by ring
      _ ≤ 1 * (K * r) * (K / r) := by gcongr
      _ = K ^ 2 := by field_simp
      _ ≤ _ := hplain
  have heq : (k ^ 2 * U + P / k) * |dz| = k ^ 2 * U * |dz| + P / k * |dz| := by ring
  rw [heq]
  rw [show 5 * K ^ 2 / r ^ 2 = 5 * (K ^ 2 / r ^ 2) by ring]
  linarith only [HR, HU, HP, HZ, HW]
