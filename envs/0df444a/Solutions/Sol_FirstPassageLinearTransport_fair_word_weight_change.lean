-- Prove2me | solution 1 for FirstPassageLinearTransport.fair_word_weight_change
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:56:01.134939+00:00
-- url     : https://prove2.me/submissions/61916cfc-0a08-45fd-bcde-b059f1b63778

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_pos
import Theorems.Thm_FirstPassageLinearTransport_collatzTilt_lt_one
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_eq_support_card
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {m : ℕ} (v : Fin m → Bool) :
    (1 / 2 : ℝ) ^ m =
      bernoulliWordWeight collatzTilt v *
        Real.exp (-(collatzFairTiltRate * (m : ℝ)) -
          collatzTiltLambda * wordIncrementSum collatzLogIncrement v) := by
  have hp : 0 < collatzTilt := collatzTilt_pos
  have hp1 : 0 < 1 - collatzTilt := sub_pos.mpr collatzTilt_lt_one
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  rw [bernoulliWordWeight_eq_support_card, wordIncrementSum_collatz]
  rw [show (1 / 2 : ℝ) ^ m =
      Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) by
    calc
      (1 / 2 : ℝ) ^ m = Real.exp (Real.log (1 / 2 : ℝ)) ^ m := by
        rw [Real.exp_log hhalf]
      _ = Real.exp ((m : ℝ) * Real.log (1 / 2 : ℝ)) :=
        (Real.exp_nat_mul _ _).symm]
  rw [show collatzTilt ^ (boolSupport v).card =
      Real.exp (((boolSupport v).card : ℝ) * Real.log collatzTilt) by
    calc
      collatzTilt ^ (boolSupport v).card =
          Real.exp (Real.log collatzTilt) ^ (boolSupport v).card := by
        rw [Real.exp_log hp]
      _ = Real.exp (((boolSupport v).card : ℝ) * Real.log collatzTilt) :=
        (Real.exp_nat_mul _ _).symm]
  rw [show (1 - collatzTilt) ^ (m - (boolSupport v).card) =
      Real.exp (((m - (boolSupport v).card : ℕ) : ℝ) *
        Real.log (1 - collatzTilt)) by
    calc
      (1 - collatzTilt) ^ (m - (boolSupport v).card) =
          Real.exp (Real.log (1 - collatzTilt)) ^
            (m - (boolSupport v).card) := by
        rw [Real.exp_log hp1]
      _ = Real.exp (((m - (boolSupport v).card : ℕ) : ℝ) *
          Real.log (1 - collatzTilt)) :=
        (Real.exp_nat_mul _ _).symm]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have hcard : (boolSupport v).card ≤ m := by
    simpa using Finset.card_le_card (Finset.subset_univ (boolSupport v))
  rw [Nat.cast_sub hcard]
  unfold collatzFairTiltRate collatzTiltLambda
  have hlog3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp [hlog3]
  ring
end FirstPassageLinearTransport
