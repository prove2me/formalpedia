-- Prove2me | solution 1 for FirstPassageLinearTransport.safeTerminalSum_le_lowerTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:20.221866+00:00
-- url     : https://prove2.me/submissions/9ceb1115-a220-46db-b891-0680e7f682f0

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliWordWeight_nonneg
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_one_eq_two_pow_mul_weight
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_le_of_not_crosses
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


attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u eps : ℝ} {r : ℕ}
    (hterminal : ∀ v : Fin r → Bool,
      ballotWordValue 1 v ≤ u →
        ((boolSupport v).card : ℝ) ≤ (3 / 4 - eps) * r) :
    safeTerminalSum u r 1 ≤
      (2 : ℝ) ^ r * threeQuarterLowerTailMass eps r := by
  classical
  unfold safeTerminalSum threeQuarterLowerTailMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  have hpow : 0 ≤ (2 : ℝ) ^ r := by positivity
  have hw : 0 ≤ bernoulliWordWeight (3 / 4) v :=
    bernoulliWordWeight_nonneg (by norm_num) (by norm_num) v
  by_cases hcross : crossesMultiplicativeFrom u r 1 v
  · simp only [hcross, if_true]
    exact mul_nonneg hpow (mul_nonneg hw (by split <;> norm_num))
  · have hvalue := ballotWordValue_le_of_not_crosses hcross
    have hsupport := hterminal v hvalue
    simp only [hcross, if_false, hsupport, if_true, mul_one]
    rw [ballotWordValue_one_eq_two_pow_mul_weight]
end FirstPassageLinearTransport
