-- Prove2me | solution 1 for FirstPassageLinearTransport.extendedWindow_shellBad_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:40:54.472001+00:00
-- url     : https://prove2.me/submissions/6388e0ff-e889-4a1c-8ea6-ec8af3af98d7

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
import Theorems.Thm_FirstPassageLinearTransport_shellBad_card_le_badCount


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta D chi Dc : ℝ} (p : StageSetup r eta)
    (hDDc : D ≤ Dc)
    (hchi0 : 0 ≤ chi)
    (hDcRate : chi * Dc ≤ quadraticWindowDensityRate eta)
    (M : ℕ) :
    ((shellBad (extendedWindow p) M).card : ℝ) ≤
      2 * quadraticWindowGlobalConstant eta *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  have hW := extendedWindow_powerDense p
  have hcardNat := shellBad_card_le_badCount (extendedWindow p) M
  have hcard :
      ((shellBad (extendedWindow p) M).card : ℝ) ≤
        (badCount (extendedWindow p) (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast hcardNat
  have hprefix := hW.bad_bound (2 ^ (M + 1))
    (Nat.one_le_pow (M + 1) 2 (by omega))
  norm_num at hprefix
  have hrate : chi * D ≤ quadraticWindowDensityRate eta := by
    exact (mul_le_mul_of_nonneg_left hDDc hchi0).trans hDcRate
  have hExp :
      ((M : ℝ) + 1) * (1 - quadraticWindowDensityRate eta) ≤
        (M : ℝ) + 1 - chi * D * M := by
    have hratePos := hW.D_pos
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  have hpow :
      ((2 : ℝ) ^ (M + 1)) ^
          (1 - quadraticWindowDensityRate eta) ≤
        (2 : ℝ) ^ ((M : ℝ) + 1 - chi * D * M) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    norm_num at hExp ⊢
    exact hExp
  have hKpos := hW.C_pos.le
  calc
    ((shellBad (extendedWindow p) M).card : ℝ) ≤
        (badCount (extendedWindow p) (2 ^ (M + 1)) : ℝ) := hcard
    _ ≤ quadraticWindowGlobalConstant eta *
        ((2 : ℝ) ^ (M + 1)) ^
          (1 - quadraticWindowDensityRate eta) := hprefix
    _ ≤ quadraticWindowGlobalConstant eta *
        (2 : ℝ) ^ ((M : ℝ) + 1 - chi * D * M) :=
      mul_le_mul_of_nonneg_left hpow hKpos
    _ = 2 * quadraticWindowGlobalConstant eta *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * ((M : ℝ) + 1 - chi * D * M) =
          Real.log 2 + (M : ℝ) * Real.log 2 +
            -(chi * D * Real.log 2 * M) by ring,
        Real.exp_add, Real.exp_add, Real.exp_log (by norm_num),
        Real.exp_nat_mul (Real.log 2) M, Real.exp_log (by norm_num)]
      ring
end FirstPassageLinearTransport
