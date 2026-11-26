-- Prove2me | solution 1 for FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:15.737091+00:00
-- url     : https://prove2.me/submissions/2b2e874c-0297-4a25-b456-799bf119a325

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
import Theorems.Thm_FirstPassageLinearTransport_variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
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
    {X h : ℕ} (hX : 4 ≤ X)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (hh : 0 < h) (hhM : h ≤ lastCompleteDyadicShell X)
    (htarget : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) →
        f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) → u n ≤ U) :
    ((1 / 4) * (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) ≤
      variableTargetHeightFailureCount f u X := by
  let b := (2 / (3 * U)) *
    (1 - reciprocalMaximumConstant / (h : ℝ))
  have hShell : b ≤
      ((shellVariableTargetHeightFailure
        (lastCompleteDyadicShell X) f u).card : ℝ) /
          (2 : ℝ) ^ lastCompleteDyadicShell X := by
    exact normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
      hhM hh hU hlog htarget hu
  by_cases hb : 0 ≤ b
  · have h := variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
      hX hb hShell
    convert h using 1 <;> dsimp [b] <;> ring
  · have hleft :
        ((1 / 4) * (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) ≤ 0 := by
      have hb' : (2 / (3 * U)) *
          (1 - reciprocalMaximumConstant / (h : ℝ)) < 0 := by
        simpa [b] using hb
      have hX0 : 0 ≤ (X : ℝ) := by positivity
      nlinarith
    exact hleft.trans (by positivity)
end FirstPassageLinearTransport
