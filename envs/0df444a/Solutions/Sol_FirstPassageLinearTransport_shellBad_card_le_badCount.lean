-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_card_le_badCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:42.839623+00:00
-- url     : https://prove2.me/submissions/8591a8d8-56ee-48a3-8c5c-4d936f3bc86f

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_prefixBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (M : ℕ) :
    (shellBad S M).card ≤ badCount S (2 ^ (M + 1)) := by
  classical
  unfold badCount
  apply Finset.card_le_card
  intro n hn
  rw [shellBad, Finset.mem_filter, mem_dyadicShell] at hn
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have hnpos : 1 ≤ n := by
    have hp : 0 < 2 ^ M := by positivity
    omega
  exact ⟨⟨hnpos, hn.1.2.le⟩, hn.2⟩
end FirstPassageLinearTransport
