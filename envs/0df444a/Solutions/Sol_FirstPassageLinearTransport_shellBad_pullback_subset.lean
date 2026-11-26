-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_pullback_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:37:34.697805+00:00
-- url     : https://prove2.me/submissions/947ffffe-1ed3-4970-9c04-638484961e8e

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) {M : ℕ} (hM : p.M0 ≤ M) :
    shellBad (firstPassagePullback p S) M ⊆
      shellBad (extendedWindow p) M ∪
        transportedSources M (targetScale r M) M
          (badTarget S (targetScale r M)) := by
  classical
  intro n hn
  rw [shellBad, Finset.mem_filter] at hn
  by_cases hnW : n ∈ extendedWindow p
  · apply Finset.mem_union_right
    have hnGood := mem_initialWindowGood_of_mem_extended_of_large p hnW (by
      simpa [log_two_eq_of_mem_dyadicShell hn.1] using hM)
    have hfp := stageLength_isFirstPassage p hM hn.1 hnGood
    have hpos := stageLength_pos p hM hn.1 hnGood
    have hle := stageLength_le_shell p hM hn.1 hnGood
    apply mem_transportedSources.mpr
    refine ⟨hn.1, stageLength p n, hpos, hle, hfp, ?_⟩
    have hnPull : n ∉ firstPassagePullback p S := hn.2
    have hnotS : stageMap p n ∉ S := by
      intro hs
      exact hnPull ⟨hnW, hs⟩
    have hlandingPos : 1 ≤ stageMap p n :=
      orbit_pos (by
        have hp : 0 < 2 ^ M := by positivity
        exact lt_of_lt_of_le hp (mem_dyadicShell.mp hn.1).1) _
    have hlandingLe : stageMap p n ≤ targetScale r M := hfp.1
    simpa [badTarget, stageMap] using
      (show stageMap p n ∈ badTarget S (targetScale r M) by
        simp [badTarget, hlandingPos, hlandingLe, hnotS])
  · apply Finset.mem_union_left
    simp [shellBad, hn.1, hnW]
end FirstPassageLinearTransport
