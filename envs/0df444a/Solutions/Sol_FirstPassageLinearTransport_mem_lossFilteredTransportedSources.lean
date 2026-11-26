-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_lossFilteredTransportedSources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:02:11.389356+00:00
-- url     : https://prove2.me/submissions/6d9d2448-845c-486a-a15a-db337f152bd1

import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_LossTransport
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M Y H n : ℕ} {B : Finset ℕ} {D : ℚ} :
    n ∈ lossFilteredTransportedSources M Y H B D ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧
          orbit h n ∈ B ∧ scaledReverseLoss Y n h ≤ D := by
  classical
  constructor
  · intro hn
    unfold lossFilteredTransportedSources at hn
    rcases Finset.mem_biUnion.mp hn with ⟨t, ht, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨y, hy, hn⟩
    have htag := mem_lossFilteredTaggedFiber.mp hn
    refine ⟨htag.1, t + 1, by omega, ?_, htag.2.1, ?_, htag.2.2.2⟩
    · exact Finset.mem_range.mp ht
    · simpa [htag.2.2.1] using hy
  · rintro ⟨hShell, h, hpos, hhH, hfp, hB, hloss⟩
    unfold lossFilteredTransportedSources
    have ht : h - 1 < H := by omega
    have htime : h - 1 + 1 = h := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨h - 1, Finset.mem_range.mpr ht, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨orbit h n, hB, ?_⟩
    simpa [htime] using
      (mem_lossFilteredTaggedFiber.mpr ⟨hShell, hfp, rfl, hloss⟩ :
        n ∈ lossFilteredTaggedFiber M Y h (orbit h n) D)
end FirstPassageLinearTransport
