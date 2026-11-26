-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotWordValue_le_of_not_crosses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:33.017698+00:00
-- url     : https://prove2.me/submissions/79999a39-4d77-4633-9800-e8025bab9fa4

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
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
theorem _root_.solution :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      ¬crossesMultiplicativeFrom u r z v →
        ballotWordValue z v ≤ u := by
  intro u r
  induction r with
  | zero =>
      intro z v hsafe
      have hzu : z ≤ u := le_of_not_gt (by
        simpa [crossesMultiplicativeFrom] using hsafe)
      simpa [ballotWordValue] using hzu
  | succ r ihr =>
      intro z v hsafe
      have hparts : ¬u < z ∧
          ¬crossesMultiplicativeFrom u r
            (z * ballotMultiplier (v 0)) (fun i => v i.succ) := by
        simpa [crossesMultiplicativeFrom] using hsafe
      rw [show ballotWordValue z v =
          ballotWordValue (z * ballotMultiplier (v 0))
            (fun i => v i.succ) by
        simp [ballotWordValue, Fin.prod_univ_succ]
        ring]
      exact ihr hparts.2
end FirstPassageLinearTransport
