-- Prove2me | solution 1 for GSCoord.appendix_II_step_C
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:22:55.618956+00:00
-- url     : https://prove2.me/submissions/500e9e1a-b1cf-4d5f-993e-24dda951854f

import Mathlib
import Definitions.Def_GSCoord_Model

open GSCoord in
theorem solution (sys : SerialSystem) (N₁ : ℕ) (hN₁ : 1 ≤ N₁) (hN₁N : N₁ < sys.N) :
    valJoint sys N₁ = valP sys := by
  unfold valJoint valP
  apply le_antisymm
  · refine le_iInf₂ fun S hS => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hS
    have hB : 0 ≤ S (N₁ + 1) := h4 (N₁ + 1) (by rw [Finset.mem_Icc]; omega)
    refine iInf₂_le (S, S (N₁ + 1)) ⟨⟨h1, rfl, h2, h3, fun k hk => h4 k ?_, fun k hk => h4 k ?_⟩, hB⟩
    · rw [Finset.mem_Icc] at hk ⊢; omega
    · rw [Finset.mem_Icc] at hk ⊢; omega
  · refine le_iInf₂ fun p hp => ?_
    obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := hp
    refine iInf₂_le p.1 ⟨h1, h3, h4, fun k hk => ?_⟩
    rw [Finset.mem_Icc] at hk
    rcases lt_trichotomy k (N₁ + 1) with hlt | heq | hgt
    · exact h5 k (by rw [Finset.mem_Icc]; omega)
    · rw [heq, h2]; exact h7
    · exact h6 k (by rw [Finset.mem_Icc]; omega)
