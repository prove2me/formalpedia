-- Prove2me | solution 1 for FirstPassageLinearTransport.landingBad_subset_insert_shellBad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:27.808809+00:00
-- url     : https://prove2.me/submissions/6850d102-7659-42b2-be93-89dae889de3e

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBad_initialWindowGood
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero


attribute [local simp] FirstPassageLinearTransport.mem_landingBad

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    landingBad q t ⊆ insert (2 ^ q) (shellInitialWindowBad (q - 1) t) := by
  classical
  intro y hy
  have hmem := mem_landingBad.mp hy
  by_cases hyTop : y = 2 ^ q
  · simp [hyTop]
  · have hyLt : y < 2 ^ q := lt_of_le_of_ne hmem.2.1 hyTop
    have hyShell : y ∈ dyadicShell (q - 1) := by
      rw [mem_dyadicShell]
      constructor
      · exact hmem.1.le
      · simpa [Nat.sub_add_cancel hq] using hyLt
    have hyBad : y ∈ shellBad (initialWindowGood t) (q - 1) := by
      rw [shellBad, Finset.mem_filter]
      exact ⟨hyShell, hmem.2.2⟩
    rw [shellBad_initialWindowGood] at hyBad
    simp [hyBad]
end FirstPassageLinearTransport
