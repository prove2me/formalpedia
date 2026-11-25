-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.topRowsBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:38.164604+00:00
-- url     : https://prove2.me/submissions/ad50d967-6c7e-42d5-b4e5-9dc3e4b19372

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : NonDegTopRows := by
  intro C k m f b v NT hC hk hm hb hv hvb hkb hNT hNTb
  have hb0 : 0 < b := by linarith
  have hC0 : 0 < C := by linarith
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < k := by linarith
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg f
  have hv0 : 0 < v := by linarith
  have hNT0 : 0 < NT := by linarith
  have hL : 0.69 < Real.log b := by
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num) hb
    linarith
  have hL0 : 0 ≤ Real.log b := by linarith
  obtain ⟨H, hH⟩ : ∃ H, H = b ^ (C * (m:ℝ) ^ 2 * f) := ⟨_, rfl⟩
  rw [← hH]
  have hH0 : 0 < H := by rw [hH]; exact Real.rpow_pos_of_pos hb0 _
  have hlogH : Real.log H = C * (m:ℝ) ^ 2 * f * Real.log b := by rw [hH, Real.log_rpow hb0]
  have hlogk : Real.log k ≤ C * Real.log b := by
    have h := Real.log_le_log hk0 hkb
    rwa [Real.log_rpow hb0] at h
  have hlogv : Real.log v ≤ Real.log b := Real.log_le_log hv0 hvb
  have hlogNT : Real.log NT ≤ C * m * f * Real.log b := by
    have h := Real.log_le_log hNT0 hNTb
    rwa [Real.log_rpow hb0] at h
  have hlogC : Real.log C ≤ C := by
    have := Real.log_le_sub_one_of_pos hC0; linarith
  have hX0 : 0 < H * NT := mul_pos hH0 hNT0
  have p1 : 0 < (C * (k:ℝ) ^ 2 * v) ^ (k * f) := pow_pos (by positivity) _
  have p2 : 0 < (H * NT) ^ (C * (k:ℝ)) := Real.rpow_pos_of_pos hX0 _
  have p3 : 0 < H ^ (C * (k:ℝ) * (m:ℝ) ^ 2) := Real.rpow_pos_of_pos hH0 _
  have e1 : Real.log ((C * (k:ℝ) ^ 2 * v) ^ (k * f)) =
      ((k:ℝ) * f) * (Real.log C + 2 * Real.log k + Real.log v) := by
    rw [Real.log_pow, Real.log_mul (mul_pos hC0 (pow_pos hk0 2)).ne' hv0.ne',
      Real.log_mul hC0.ne' (pow_pos hk0 2).ne', Real.log_pow]
    push_cast; try ring
  have e2 : Real.log ((H * NT) ^ (C * (k:ℝ))) = C * k * (C * (m:ℝ) ^ 2 * f * Real.log b + Real.log NT) := by
    rw [Real.log_rpow hX0, Real.log_mul hH0.ne' hNT0.ne', hlogH]
  have e3 : Real.log (H ^ (C * (k:ℝ) * (m:ℝ) ^ 2)) = C * k * (m:ℝ) ^ 2 * (C * (m:ℝ) ^ 2 * f * Real.log b) := by
    rw [Real.log_rpow hH0, hlogH]
  have hpos := mul_pos (mul_pos p1 p2) p3
  rw [← Real.exp_log hpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (mul_pos p1 p2).ne' p3.ne', Real.log_mul p1.ne' p2.ne', e1, e2, e3]
  have hK : 0 ≤ (k:ℝ) * f := mul_nonneg hk0.le hf0
  have hu1 : 1 ≤ C ^ 2 * (m:ℝ) ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hm1)
  have hCu : C ≤ C ^ 2 * (m:ℝ) ^ 4 := by
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * (C * (m:ℝ) ^ 4) :=
          mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hm1)) hC0.le
      _ = C ^ 2 * (m:ℝ) ^ 4 := by ring
  have hm24 : (m:ℝ) ^ 2 ≤ (m:ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm14 : (m:ℝ) ≤ (m:ℝ) ^ 4 := by
    calc (m:ℝ) = (m:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (m:ℝ) ^ 4 := pow_le_pow_right₀ hm1 (by norm_num)
  have hKu : 0 ≤ (k:ℝ) * f * (C ^ 2 * (m:ℝ) ^ 4) := by positivity
  have hP5 : 0 ≤ C ^ 2 * (k:ℝ) * f * Real.log b := by positivity
  have hCk0 : 0 ≤ C * (k:ℝ) := by positivity
  have F1 := mul_le_mul_of_nonneg_left hlogC hK
  have KoszulLowersPower := mul_le_mul_of_nonneg_left hCu hK
  have KoszulImageInIdeal := mul_le_mul_of_nonneg_left hL.le hKu
  have F3 := mul_le_mul_of_nonneg_left hlogk hK
  have F3b := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCu hL0) hK
  have F4 := mul_le_mul_of_nonneg_left hlogv hK
  have F4b := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hL0 hu1) hK
  have F5 := mul_le_mul_of_nonneg_left hm24 hP5
  have F6 := mul_le_mul_of_nonneg_left hlogNT hCk0
  have DiagonalTruncatedIntegralZero := mul_le_mul_of_nonneg_left hm14 hP5
  linarith
end Formalism.HermitianLatticeCounting.P
