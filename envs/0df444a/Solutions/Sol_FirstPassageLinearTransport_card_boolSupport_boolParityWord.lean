-- Prove2me | solution 1 for FirstPassageLinearTransport.card_boolSupport_boolParityWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:40.9608+00:00
-- url     : https://prove2.me/submissions/a4d928ea-eb8f-482b-b892-be314699d3b0

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
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
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (m n : ℕ) :
    (boolSupport (boolParityWord m n)).card = oddCount n m := by
  have hfin : ∀ b : Fin 2,
      (if finTwoEquiv b = true then 1 else 0) = (b : ℕ) := by
    intro b
    fin_cases b <;> rfl
  unfold boolSupport boolParityWord oddCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ i : Fin m,
        if finTwoEquiv (parityBit n i) = true then 1 else 0) =
        ∑ i : Fin m, (parityBit n i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact hfin (parityBit n i)
    _ = ∑ i ∈ Finset.range m, (parityBit n i : ℕ) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (fun i => (parityBit n i : ℕ)) m)
end FirstPassageLinearTransport
