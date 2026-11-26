-- Prove2me | solution 1 for FirstPassageLinearTransport.card_shellVariableTargetHeightFailure_le_failureCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:34:16.511016+00:00
-- url     : https://prove2.me/submissions/fe539dd9-e020-4735-998c-b847260d0f47

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
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
    {M X : ℕ} {f u : ℕ → ℝ}
    (hMX : 2 ^ (M + 1) ≤ X + 1) :
    (shellVariableTargetHeightFailure M f u).card ≤
      variableTargetHeightFailureCount f u X := by
  classical
  let emb : {n : ℕ // n ∈ dyadicShell M} ↪ ℕ :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hsub :
      (shellVariableTargetHeightFailure M f u).map emb ⊆
        (Finset.Icc 1 X).filter fun n =>
          ¬HasVariableTargetHeightWitness f u n := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hn
    have hmFailure := hm
    simp only [shellVariableTargetHeightFailure, Finset.mem_filter,
      Finset.mem_univ, true_and] at hmFailure
    have hnBounds := mem_dyadicShell.mp m.2
    have hnPos : 1 ≤ m.1 := by
      have hpow : 0 < 2 ^ M := by positivity
      omega
    have hnX : m.1 ≤ X := by omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hnPos, hnX⟩, hmFailure⟩
  calc
    (shellVariableTargetHeightFailure M f u).card =
        ((shellVariableTargetHeightFailure M f u).map emb).card := by
      rw [Finset.card_map]
    _ ≤ ((Finset.Icc 1 X).filter fun n =>
        ¬HasVariableTargetHeightWitness f u n).card :=
      Finset.card_le_card hsub
    _ = variableTargetHeightFailureCount f u X := rfl
end FirstPassageLinearTransport
