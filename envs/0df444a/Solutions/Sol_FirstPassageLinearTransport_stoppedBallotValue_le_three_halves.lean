-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedBallotValue_le_three_halves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:08.449998+00:00
-- url     : https://prove2.me/submissions/2e129ce1-201e-44c2-890e-a29fa5d240b8

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
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

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      0 ≤ u → 0 ≤ z → z ≤ 3 * u / 2 →
        stoppedBallotValue u r z v ≤ 3 * u / 2 := by
  intro u r
  induction r with
  | zero => intro z v hu hz hzUpper; simpa [stoppedBallotValue] using hzUpper
  | succ r ihr =>
      intro z v hu hz hzUpper
      by_cases hcross : u < z
      · simpa [stoppedBallotValue, hcross] using hzUpper
      · simp only [stoppedBallotValue, hcross, if_false]
        have hzu : z ≤ u := le_of_not_gt hcross
        have hmult0 : 0 ≤ ballotMultiplier (v 0) := by
          cases v 0 <;> norm_num [ballotMultiplier]
        apply ihr hu (mul_nonneg hz hmult0)
        cases hbit : v 0 <;> simp [ballotMultiplier, hbit]
        · nlinarith
        · nlinarith
end FirstPassageLinearTransport
