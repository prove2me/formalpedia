-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotWordValue_one_eq_exp_incrementSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:30.496119+00:00
-- url     : https://prove2.me/submissions/c6c34b31-b6de-45f6-afc1-5f60e0164838

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotMultiplier_eq_exp_collatzLogIncrement
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
    {r : ℕ} (v : Fin r → Bool) :
    ballotWordValue 1 v =
      Real.exp (wordIncrementSum collatzLogIncrement v) := by
  unfold ballotWordValue wordIncrementSum
  simp only [one_mul]
  rw [show (∏ i, ballotMultiplier (v i)) =
      ∏ i, Real.exp (collatzLogIncrement (v i)) by
    apply Finset.prod_congr rfl
    intro i _hi
    exact ballotMultiplier_eq_exp_collatzLogIncrement (v i)]
  exact (Real.exp_sum Finset.univ
    (fun i => collatzLogIncrement (v i))).symm
end FirstPassageLinearTransport
