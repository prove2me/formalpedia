-- Prove2me | solution 1 for BianchiIX.partial_core_radial_derivative_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:48:31.625571+00:00
-- url     : https://prove2.me/submissions/3f1c5de0-a23f-43ba-85f5-1c221518a471

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


/-- The moving-entry response retains the weak amplitude after substitution of radial scales. -/
theorem solution {r K k U P dR dU dP dz : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hk : 0 < k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hU : 0 ≤ U) (hP : 0 ≤ P ∧ P ≤ 1)
    (hR : |dR| ≤ K / r ^ 2) (hdU : |dU| ≤ K * U / r)
    (hdP : |dP| ≤ K * P / r) (hdz : |dz| ≤ K / r) :
    |dU| + (U + P) * (|dR| + |dP|) / k + (k * U + P ^ 2 / k) * |dz| ≤
      4 * K ^ 2 * (U + r * P) / r ^ 2 := by
  have hr0 := hr.1
  have hP0 := hP.1
  let B := (U + r * P) / r ^ 2
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hB : 0 ≤ B := div_nonneg (add_nonneg hU (mul_nonneg hr.1.le hP.1)) (sq_nonneg r)
  have hUP : 0 ≤ U + P := add_nonneg hU hP.1
  have hPr : 0 ≤ P * r ∧ P * r ≤ 1 :=
    ⟨mul_nonneg hP.1 hr.1.le, (mul_le_mul_of_nonneg_right hP.2 hr.1.le).trans (by simpa using hr.2)⟩
  have hUscale : U / r ≤ B := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr.1)).mp
    dsimp [B]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hr.2 hU, mul_nonneg hr.1.le hP.1]
  have hUPscale : (U + P) / r ≤ B := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr.1)).mp
    dsimp [B]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_left hr.2 hU]
  have hUPplain : U + P ≤ B := le_trans (by
    apply (le_div_iff₀ hr.1).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr.2 hUP) hUPscale
  have hPscale : (U + P) * P ≤ B :=
    (mul_le_of_le_one_right hUP hP.2).trans hUPplain
  have hmix : U / r ^ 2 + P ^ 2 ≤ B := by
    apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hr.1)).mp
    dsimp [B]
    field_simp
    nlinarith only [mul_le_mul_of_nonneg_right hPr.2 hPr.1]
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have HU : |dU| ≤ K ^ 2 * B := hdU.trans (calc
    _ = K * (U / r) := by ring
    _ ≤ K * B := mul_le_mul_of_nonneg_left hUscale hK0
    _ ≤ K ^ 2 * B := mul_le_mul_of_nonneg_right hKK hB)
  have HR : (U + P) * |dR| / k ≤ K ^ 2 * B := by
    calc
      _ = (U + P) * |dR| * (1 / k) := by ring
      _ ≤ (U + P) * (K / r ^ 2) * (K * r) := by gcongr
      _ = K ^ 2 * ((U + P) / r) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hUPscale (sq_nonneg K)
  have HP : (U + P) * |dP| / k ≤ K ^ 2 * B := by
    calc
      _ = (U + P) * |dP| * (1 / k) := by ring
      _ ≤ (U + P) * (K * P / r) * (K * r) := by gcongr
      _ = K ^ 2 * ((U + P) * P) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hPscale (sq_nonneg K)
  have HZ : (k * U + P ^ 2 / k) * |dz| ≤ K ^ 2 * B := by
    calc
      _ = (k * U + P ^ 2 * (1 / k)) * |dz| := by ring
      _ ≤ ((K / r) * U + P ^ 2 * (K * r)) * (K / r) := by gcongr
      _ = K ^ 2 * (U / r ^ 2 + P ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hmix (sq_nonneg K)
  have heq : (U + P) * (|dR| + |dP|) / k =
      (U + P) * |dR| / k + (U + P) * |dP| / k := by ring
  rw [heq]
  rw [show 4 * K ^ 2 * (U + r * P) / r ^ 2 = 4 * K ^ 2 * B by dsimp [B]; ring]
  linarith only [HU, HR, HP, HZ]
