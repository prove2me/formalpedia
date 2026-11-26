-- Prove2me | solution 1 for FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:34.266322+00:00
-- url     : https://prove2.me/submissions/eb301293-2771-4e3c-8852-af419534b116

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Theorems.Thm_FirstPassageLinearTransport_card_shellVariableTargetHeightFailure_le_failureCount
import Theorems.Thm_FirstPassageLinearTransport_pow_lastCompleteDyadicShell_succ_le
import Theorems.Thm_FirstPassageLinearTransport_X_lt_four_mul_pow_lastCompleteDyadicShell
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {X : ℕ} (hX : 4 ≤ X) {f u : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hShell : b ≤
      ((shellVariableTargetHeightFailure
        (lastCompleteDyadicShell X) f u).card : ℝ) /
          (2 : ℝ) ^ lastCompleteDyadicShell X) :
    (b / 4) * (X : ℝ) ≤ variableTargetHeightFailureCount f u X := by
  let M := lastCompleteDyadicShell X
  have hpowPos : 0 < (2 : ℝ) ^ M := by positivity
  have hShellMul : b * (2 : ℝ) ^ M ≤
      (shellVariableTargetHeightFailure M f u).card := by
    exact (le_div_iff₀ hpowPos).mp (by simpa [M] using hShell)
  have hXpowNat : X < 4 * 2 ^ M := by
    simpa [M] using X_lt_four_mul_pow_lastCompleteDyadicShell hX
  have hXpow : (X : ℝ) ≤ 4 * (2 : ℝ) ^ M := by
    exact_mod_cast hXpowNat.le
  have hscaled : (b / 4) * (X : ℝ) ≤ b * (2 : ℝ) ^ M := by
    nlinarith
  have hcardCount := card_shellVariableTargetHeightFailure_le_failureCount
    (f := f) (u := u)
    (show 2 ^ (M + 1) ≤ X + 1 by
      have hpow := pow_lastCompleteDyadicShell_succ_le hX
      dsimp [M]
      omega)
  have hcardCountR :
      ((shellVariableTargetHeightFailure M f u).card : ℝ) ≤
        variableTargetHeightFailureCount f u X := by
    exact_mod_cast hcardCount
  exact hscaled.trans (hShellMul.trans hcardCountR)
end FirstPassageLinearTransport
