-- Prove2me | solution 1 for BianchiIX.partial_core_connection_wall_budget
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:28:18.90993+00:00
-- url     : https://prove2.me/submissions/2e4e6fa6-e1ed-4111-8395-ffbff12e0840

import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.GCongr

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_log_bound {k : ℝ} (hk : 6 ≤ k) : Real.log (4 * k) ≤ k := by
  have hk0 : 0 ≤ k := by linarith
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 4 * k)).mpr
  have H := Real.quadratic_le_exp_of_nonneg hk0
  nlinarith only [hk, H, sq_nonneg (k - 6)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_strong_log_budget {k : ℝ} (hk : 6 ≤ k) :
    Real.exp (-k / 24) * Real.log (4 * k) ≤ 24 := by
  have hk0 : 0 ≤ k := by linarith only [hk]
  have H := affine_mul_exp_neg_le_one (k / 24)
  rw [show -(k / 24) = -k / 24 by ring] at H
  have HE := Real.exp_pos (-k / 24)
  have Hk : Real.exp (-k / 24) * k ≤ 24 := by nlinarith only [H, HE]
  exact (mul_le_mul_of_nonneg_left (core_log_bound hk) HE.le).trans Hk

end
end


/-- The strong-wall exponential absorbs the logarithm and the extra inverse radial scale. -/
theorem solution {r K k A B U P u w du dw : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hk : 6 ≤ k)
    (hki : 1 / k ≤ K * r) (hkhi : k ≤ K / r)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (_hu : 0 ≤ u) (hw : 0 ≤ w)
    (hdec : u ≤ U * Real.exp (-k / 12)) (hweak : w ≤ P)
    (hdu : |du| ≤ u * (K / r + A * Real.log (4 * k) / r ^ 2))
    (hdw : |dw| ≤ w * (K / r + B * Real.log (4 * k))) :
    u ≤ U ∧ r * |du| ≤ K * (1 + 576 * A) * U ∧
      r * |dw| ≤ K * (1 + B) * P := by
  have hk0 : 0 < k := by linarith only [hk]
  have hP : 0 ≤ P := hw.trans hweak
  have hL : 0 ≤ Real.log (4 * k) := Real.log_nonneg (by linarith only [hk])
  have hE : Real.exp (-k / 12) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hk])
  have hue : u ≤ U := hdec.trans (mul_le_of_le_one_right hU hE)
  have hkinv : 1 / r ≤ K * k := by
    apply (div_le_iff₀ hr).mpr
    nlinarith only [(div_le_iff₀ hk0).mp hki]
  have Hlin : k * Real.exp (-k / 24) ≤ 24 := by
    have H := affine_mul_exp_neg_le_one (k / 24)
    rw [show -(k / 24) = -k / 24 by ring] at H
    nlinarith only [H, Real.exp_pos (-k / 24)]
  have Hlog : Real.exp (-k / 12) * Real.log (4 * k) / r ≤ 576 * K := by
    calc
      _ = (Real.exp (-k / 24) * Real.log (4 * k)) * Real.exp (-k / 24) * (1 / r) := by
        rw [show -k / 12 = -k / 24 + -k / 24 by ring, Real.exp_add]
        ring
      _ ≤ (Real.exp (-k / 24) * Real.log (4 * k)) * Real.exp (-k / 24) * (K * k) := by gcongr
      _ = K * (Real.exp (-k / 24) * Real.log (4 * k)) * (k * Real.exp (-k / 24)) := by ring
      _ ≤ K * 24 * 24 := by gcongr; exact partial_core_strong_log_budget hk
      _ = _ := by ring
  have HU : r * |du| ≤ U * (K * Real.exp (-k / 12) +
      A * (Real.exp (-k / 12) * Real.log (4 * k) / r)) := by
    calc
      _ ≤ r * (u * (K / r + A * Real.log (4 * k) / r ^ 2)) := mul_le_mul_of_nonneg_left hdu hr.le
      _ ≤ r * ((U * Real.exp (-k / 12)) * (K / r + A * Real.log (4 * k) / r ^ 2)) := by gcongr
      _ = _ := by field_simp
  have HW : K / r + B * Real.log (4 * k) ≤ K * (1 + B) / r := by
    calc
      _ ≤ K / r + B * k := add_le_add le_rfl (mul_le_mul_of_nonneg_left (core_log_bound hk) hB)
      _ ≤ K / r + B * (K / r) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hkhi hB)
      _ = _ := by ring
  refine ⟨hue, HU.trans ?_, ?_⟩
  · calc
      _ ≤ U * (K * 1 + A * (576 * K)) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ r * (w * (K / r + B * Real.log (4 * k))) := mul_le_mul_of_nonneg_left hdw hr.le
      _ ≤ r * (P * (K * (1 + B) / r)) := by gcongr
      _ = _ := by field_simp
