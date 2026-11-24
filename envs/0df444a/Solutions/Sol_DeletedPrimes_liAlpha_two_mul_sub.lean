-- Prove2me | solution 1 for DeletedPrimes.liAlpha_two_mul_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:28.720518+00:00
-- url     : https://prove2.me/submissions/b2f363d2-d124-4638-b9b4-6786784cad29

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
import Theorems.Thm_DeletedPrimes_intervalIntegrable_liAlpha_integrand

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {α X : ℝ} (hα1 : α ≤ 1) (hX : 2 ≤ X) :
    2 ^ (α - 2) * X ^ α / Real.log X ≤ liAlpha α (2 * X) - liAlpha α X := by
  have hX0 : 0 < X := by linarith
  have hdiff : liAlpha α (2 * X) - liAlpha α X = ∫ u in X..2 * X, u ^ (α - 1) / Real.log u :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_liAlpha_integrand α le_rfl (by linarith))
      (intervalIntegrable_liAlpha_integrand α le_rfl hX)
  rw [hdiff]
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL2 : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    linarith
  have hL2pos : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hmono : ∫ _u in X..2 * X, (2 * X) ^ (α - 1) / Real.log (2 * X)
      ≤ ∫ u in X..2 * X, u ^ (α - 1) / Real.log u := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegrable_liAlpha_integrand α hX (by linarith))
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_nonpos hu0 hu.2 (by linarith))
      (Real.log_pos (by linarith [hu.1])) (Real.log_le_log hu0 hu.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  have e1 : (2 * X) ^ (α - 1) = 2 ^ (α - 1) * X ^ (α - 1) := Real.mul_rpow (by norm_num) hX0.le
  have e2 : X ^ α = X * X ^ (α - 1) := by
    conv_lhs => rw [show α = 1 + (α - 1) by ring]
    rw [Real.rpow_add hX0, Real.rpow_one]
  have e3 : (2 : ℝ) ^ (α - 2) = 2 ^ (α - 1) / 2 := by
    rw [show α - 2 = (α - 1) - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
  have hA : 0 < (2 : ℝ) ^ (α - 1) * X ^ α := by positivity
  calc 2 ^ (α - 2) * X ^ α / Real.log X = (2 ^ (α - 1) * X ^ α) / (2 * Real.log X) := by
        rw [e3]; field_simp
    _ ≤ (2 ^ (α - 1) * X ^ α) / Real.log (2 * X) := div_le_div_of_nonneg_left hA.le hL2pos hL2
    _ = (2 * X - X) * ((2 * X) ^ (α - 1) / Real.log (2 * X)) := by
        rw [e1, e2]; field_simp; ring
end DeletedPrimes
