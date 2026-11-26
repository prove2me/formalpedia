-- Prove2me | solution 1 for FirstPassageLinearTransport.ballotWordValue_one_eq_two_pow_mul_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:58:18.238592+00:00
-- url     : https://prove2.me/submissions/d7c2f4c8-a3d5-4261-a7d4-6f14f15d8da2

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
    ∀ {r : ℕ} (v : Fin r → Bool),
      ballotWordValue 1 v =
        (2 : ℝ) ^ r * bernoulliWordWeight (3 / 4) v := by
  intro r
  induction r with
  | zero => intro v; simp [ballotWordValue, bernoulliWordWeight]
  | succ r ihr =>
      intro v
      let b := v 0
      let w : Fin r → Bool := fun i => v i.succ
      have hv : v = Fin.cons b w := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hv, ballotWordValue_cons,
        ballotWordValue_scale, ihr, bernoulliWordWeight_cons, pow_succ]
      cases b <;> norm_num [ballotMultiplier]
      <;> ring
end FirstPassageLinearTransport
