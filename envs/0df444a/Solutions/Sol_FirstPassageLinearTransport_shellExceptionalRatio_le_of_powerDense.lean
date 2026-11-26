-- Prove2me | solution 1 for FirstPassageLinearTransport.shellExceptionalRatio_le_of_powerDense
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:50:11.143796+00:00
-- url     : https://prove2.me/submissions/8a5d46bc-e727-4a86-baa5-4abb5cce61a5

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBad_card_le_badCount
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ} (hS : PowerDense S C D) (M : ℕ) :
    shellExceptionalRatio S M ≤
      2 * C * Real.exp (-(Real.log 2 * D * M)) := by
  have hcardNat := shellBad_card_le_badCount S M
  have hcard :
      ((shellBad S M).card : ℝ) ≤
        (badCount S (2 ^ (M + 1)) : ℝ) := by
    exact_mod_cast hcardNat
  have hbad := hS.bad_bound (2 ^ (M + 1))
    (Nat.one_le_pow (M + 1) 2 (by omega))
  have hraw :
      shellExceptionalRatio S M ≤
        C * ((2 : ℝ) ^ (M + 1)) ^ (1 - D) / (2 : ℝ) ^ M := by
    unfold shellExceptionalRatio
    apply (div_le_div_iff_of_pos_right (by positivity)).2
    exact hcard.trans (by simpa using hbad)
  calc
    shellExceptionalRatio S M
        ≤ C * ((2 : ℝ) ^ (M + 1)) ^ (1 - D) /
            (2 : ℝ) ^ M := hraw
    _ = C * (2 : ℝ) ^ (((M : ℝ) + 1) * (1 - D) - M) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      have hmul :
          ((2 : ℝ) ^ ((M + 1 : ℕ) : ℝ)) ^ (1 - D) =
            (2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      rw [hmul]
      calc
        C * (2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) /
              (2 : ℝ) ^ (M : ℝ)
            = C * ((2 : ℝ) ^ (((M + 1 : ℕ) : ℝ) * (1 - D)) /
              (2 : ℝ) ^ (M : ℝ)) := by ring
        _ = C * (2 : ℝ) ^
              ((((M + 1 : ℕ) : ℝ) * (1 - D)) - (M : ℝ)) := by
              rw [Real.rpow_sub (by norm_num)]
        _ = C * (2 : ℝ) ^ (((M : ℝ) + 1) * (1 - D) - M) := by
              push_cast
              rfl
    _ ≤ C * (2 : ℝ) ^ (1 - D * M) := by
      apply mul_le_mul_of_nonneg_left _ hS.C_pos.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      nlinarith [hS.D_pos]
    _ = 2 * C * Real.exp (-(Real.log 2 * D * M)) := by
      rw [show (1 : ℝ) - D * M = 1 + -(D * M) by ring,
        Real.rpow_add (by norm_num), Real.rpow_one,
        Real.rpow_def_of_pos (by norm_num)]
      ring_nf
end FirstPassageLinearTransport
