-- Prove2me | solution 1 for FirstPassageLinearTransport.mem_transportedSources
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:00:27.313964+00:00
-- url     : https://prove2.me/submissions/54b064d7-ddc0-4f71-adb4-4bc1f1f85e60

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
namespace FirstPassageLinearTransport
theorem _root_.solution {M Y H n : ℕ} {B : Finset ℕ} :
    n ∈ transportedSources M Y H B ↔
      n ∈ dyadicShell M ∧
        ∃ h : ℕ, 1 ≤ h ∧ h ≤ H ∧ IsFirstPassage Y n h ∧ orbit h n ∈ B := by
  classical
  constructor
  · intro hn
    unfold transportedSources at hn
    rcases Finset.mem_biUnion.mp hn with ⟨t, ht, hn⟩
    rcases Finset.mem_biUnion.mp hn with ⟨y, hy, hn⟩
    have htag := mem_taggedFiber.mp hn
    refine ⟨htag.1, t + 1, by omega, ?_, htag.2.1, ?_⟩
    · exact Finset.mem_range.mp ht
    · simpa [htag.2.2] using hy
  · rintro ⟨hShell, h, hpos, hhH, hfp, hB⟩
    unfold transportedSources
    have ht : h - 1 < H := by omega
    have htime : h - 1 + 1 = h := by omega
    apply Finset.mem_biUnion.mpr
    refine ⟨h - 1, Finset.mem_range.mpr ht, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨orbit h n, hB, ?_⟩
    simpa [htime] using
      (mem_taggedFiber.mpr ⟨hShell, hfp, rfl⟩ :
        n ∈ taggedFiber M Y h (orbit h n))
end FirstPassageLinearTransport
