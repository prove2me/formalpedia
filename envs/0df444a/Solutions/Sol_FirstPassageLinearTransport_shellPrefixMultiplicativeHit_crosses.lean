-- Prove2me | solution 1 for FirstPassageLinearTransport.shellPrefixMultiplicativeHit_crosses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:33:25.517212+00:00
-- url     : https://prove2.me/submissions/609fa164-1a79-41a4-afdd-469e073d8f35

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_dyadicShellPrefixEquiv_second_mod
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_boolParityWord_mod
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ}
    {n : {n : ℕ // n ∈ dyadicShell M}}
    (hn : n ∈ shellPrefixMultiplicativeHit M h hhM u) :
    crossesMultiplicativeFrom u h 1 (boolParityWord h n.1) := by
  classical
  have hnResidue :
      (dyadicShellPrefixEquiv M h hhM n).2 ∈
        multiplicativeHitResidues h u := by
    simpa [shellPrefixMultiplicativeHit, shellPrefixResidueSet] using hn
  have hcrossCode :
      crossesMultiplicativeFrom u h 1
        (boolParityCode h (dyadicShellPrefixEquiv M h hhM n).2) := by
    rw [multiplicativeHitResidues] at hnResidue
    exact (Finset.mem_filter.mp hnResidue).2
  have hword :
      boolParityCode h (dyadicShellPrefixEquiv M h hhM n).2 =
        boolParityWord h n.1 := by
    rw [boolParityCode_eq_word]
    change boolParityWord h
        ((dyadicShellPrefixEquiv M h hhM n).2 : ℕ) =
      boolParityWord h n.1
    rw [dyadicShellPrefixEquiv_second_mod, boolParityWord_mod]
  rwa [hword] at hcrossCode
end FirstPassageLinearTransport
