-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedTree_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:01.349826+00:00
-- url     : https://prove2.me/submissions/6be10b5c-ee32-47d0-b42c-60a4dffea747

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_sum_stoppedBallotValue_eq
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_le_three_halves
import Theorems.Thm_FirstPassageLinearTransport_not_crosses_stopped_eq_wordValue
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
theorem _root_.solution
    {u : ℝ} (hu : 1 ≤ u) (r : ℕ) :
    (2 : ℝ) ^ r ≤
      (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) +
        safeTerminalSum u r 1 := by
  classical
  have hu0 : 0 ≤ u := zero_le_one.trans hu
  have hupper : (1 : ℝ) ≤ 3 * u / 2 := by nlinarith
  have hmean :
      ∑ v : Fin r → Bool, stoppedBallotValue u r 1 v =
        (2 : ℝ) ^ r := by
    simpa using sum_stoppedBallotValue_eq u r 1
  rw [← hmean]
  calc
    (∑ v : Fin r → Bool, stoppedBallotValue u r 1 v) ≤
        ∑ v : Fin r → Bool,
          (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2
            else ballotWordValue 1 v) := by
      apply Finset.sum_le_sum
      intro v _hv
      by_cases hv : crossesMultiplicativeFrom u r 1 v
      · simp only [hv, if_true]
        exact stoppedBallotValue_le_three_halves hu0 (by norm_num) hupper
      · simp only [hv, if_false]
        exact (not_crosses_stopped_eq_wordValue hv).le
    _ = (multiplicativeHitCount u r 1 : ℝ) * (3 * u / 2) +
        safeTerminalSum u r 1 := by
      unfold multiplicativeHitCount safeTerminalSum
      rw [show (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2
              else ballotWordValue 1 v)) =
          (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 3 * u / 2 else 0)) +
          (∑ v : Fin r → Bool,
            (if crossesMultiplicativeFrom u r 1 v then 0
              else ballotWordValue 1 v)) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro v _hv
        split <;> simp_all]
      congr 1
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
end FirstPassageLinearTransport
