-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:04:34.130957+00:00
-- url     : https://prove2.me/submissions/f830c14b-602c-4973-bd08-6987003386fe

import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y n : ℕ} {times B : Finset ℕ} {D : ℚ} :
    n ∈ lossFilteredTransportedSourcesAtTimes M Y times B D ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, h ∈ times ∧ IsFirstPassage Y n h ∧
          orbit h n ∈ B ∧ scaledReverseLoss Y n h ≤ D := by
  classical
  constructor
  · intro hn
    unfold lossFilteredTransportedSourcesAtTimes at hn
    rcases Finset.mem_biUnion.mp hn with ⟨h, hh, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨y, hy, hn⟩
    have htag := mem_lossFilteredTaggedFiber.mp hn
    exact ⟨htag.1, h, hh, htag.2.1, by simpa [htag.2.2.1] using hy,
      htag.2.2.2⟩
  · rintro ⟨hShell, h, hh, hfp, hB, hloss⟩
    unfold lossFilteredTransportedSourcesAtTimes
    apply Finset.mem_biUnion.mpr
    refine ⟨h, hh, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨orbit h n, hB, ?_⟩
    exact mem_lossFilteredTaggedFiber.mpr ⟨hShell, hfp, rfl, hloss⟩
end FirstPassageLinearTransport
