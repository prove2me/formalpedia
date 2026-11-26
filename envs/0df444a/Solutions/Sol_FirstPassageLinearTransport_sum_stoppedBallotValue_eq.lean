-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_stoppedBallotValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:57:46.851384+00:00
-- url     : https://prove2.me/submissions/bc3700e1-5a02-4679-b22f-eac8d8cc1e6f

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
    ∀ (u : ℝ) (r : ℕ) (z : ℝ),
      ∑ v : Fin r → Bool, stoppedBallotValue u r z v =
        (2 : ℝ) ^ r * z := by
  intro u r
  induction r with
  | zero => intro z; simp [stoppedBallotValue]
  | succ r ihr =>
      intro z
      rw [← Equiv.sum_comp
        (Fin.consEquiv (fun _ : Fin (r + 1) => Bool))]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      by_cases hz : u < z
      · simp [Fin.consEquiv, stoppedBallotValue, hz, pow_succ]
        ring
      · simp [Fin.consEquiv, stoppedBallotValue_cons, hz]
        rw [ihr, ihr, pow_succ]
        norm_num [ballotMultiplier]
        ring
end FirstPassageLinearTransport
