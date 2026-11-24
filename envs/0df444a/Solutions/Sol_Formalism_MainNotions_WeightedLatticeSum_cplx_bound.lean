-- Prove2me | solution 1 for Formalism.MainNotions.WeightedLatticeSum.cplx_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:08:34.095813+00:00
-- url     : https://prove2.me/submissions/af1526e3-3631-4c14-8e73-c41fa953481e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_WeightedLatticeSum
import Theorems.Thm_Formalism_MainNotions_WeightedLatticeSum_rpow_neg_three_halves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.WeightedLatticeSum
open Finset
private theorem rpow_neg_three_halves_anti_of_one_le {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    t ^ (-(3 / 2 : ℝ)) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  rw [rpow_neg_three_halves hs0, rpow_neg_three_halves ht0]
  apply one_div_le_one_div_of_le (mul_pos hs0 (Real.sqrt_pos.mpr hs0))
  exact mul_le_mul hst (Real.sqrt_le_sqrt hst) (Real.sqrt_nonneg _) ht0.le
private theorem rpow_neg_three_le_mul_rpow_neg_three_halves {A B C : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hAC : A ≤ C) (hBC : B ≤ C) :
    C ^ (-(3 : ℝ)) ≤ A ^ (-(3 / 2 : ℝ)) * B ^ (-(3 / 2 : ℝ)) := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hC0 : 0 < C := by linarith
  rw [← Real.mul_rpow hA0.le hB0.le]
  have e : C ^ (-(3 : ℝ)) = (C * C) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.mul_rpow hC0.le hC0.le, ← Real.rpow_add hC0]
    norm_num
  rw [e]
  exact rpow_neg_three_halves_anti_of_one_le (by nlinarith) (mul_le_mul hAC hBC hB0.le hC0.le)
end Formalism.MainNotions.WeightedLatticeSum
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.WeightedLatticeSum
open Finset
namespace Formalism.MainNotions.WeightedLatticeSum
theorem _root_.solution (R : ℝ) (hR : 0 < R) (z : ℂ) :
    (max 1 (‖z‖ / R)) ^ (-(3 : ℝ)) ≤
      (max 1 (|z.re| / R)) ^ (-(3 / 2 : ℝ)) * (max 1 (|z.im| / R)) ^ (-(3 / 2 : ℝ)) := by
  have h1 : |z.re| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) (inv_nonneg.mpr hR.le)
  have h2 : |z.im| / R ≤ ‖z‖ / R := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) (inv_nonneg.mpr hR.le)
  exact rpow_neg_three_le_mul_rpow_neg_three_halves (le_max_left _ _) (le_max_left _ _) (max_le_max le_rfl h1)
    (max_le_max le_rfl h2)
end Formalism.MainNotions.WeightedLatticeSum
