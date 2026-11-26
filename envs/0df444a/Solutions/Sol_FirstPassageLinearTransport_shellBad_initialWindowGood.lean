-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_initialWindowGood
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:10.71207+00:00
-- url     : https://prove2.me/submissions/68645e5d-6ee5-45f5-ab1f-f3f82b27d9df

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
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



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (t : ℝ) (M : ℕ) :
    shellBad (initialWindowGood t) M = shellInitialWindowBad M t := by
  classical
  ext n
  constructor
  · intro hn
    rw [shellBad, Finset.mem_filter] at hn
    have hlog := log_two_eq_of_mem_dyadicShell hn.1
    rw [initialWindowGood, Set.mem_setOf_eq] at hn
    push_neg at hn
    rcases hn.2 with ⟨k, hk, hfail⟩
    rw [shellInitialWindowBad, Finset.mem_filter]
    refine ⟨hn.1, k, by simpa [hlog] using hk, ?_⟩
    by_cases hlower :
        centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤ (orbit k n : ℝ)
    · exact Or.inr (hfail hlower)
    · exact Or.inl (lt_of_not_ge hlower)
  · intro hn
    rw [shellInitialWindowBad, Finset.mem_filter] at hn
    have hlog := log_two_eq_of_mem_dyadicShell hn.1
    rw [shellBad, Finset.mem_filter]
    refine ⟨hn.1, ?_⟩
    rw [initialWindowGood, Set.mem_setOf_eq]
    push_neg
    rcases hn.2 with ⟨k, hk, hfail⟩
    refine ⟨k, by simpa [hlog] using hk, ?_⟩
    intro hlower
    rcases hfail with hfail | hfail
    · exact False.elim ((not_lt_of_ge hlower) hfail)
    · exact hfail
end FirstPassageLinearTransport
