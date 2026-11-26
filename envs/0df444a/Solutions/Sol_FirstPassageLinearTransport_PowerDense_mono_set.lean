-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.mono_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:41.856195+00:00
-- url     : https://prove2.me/submissions/c0f4997f-18f6-4083-9f26-f15c33f3be81

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_bad_bound
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



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S T : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) (hST : S ⊆ T) :
    PowerDense T C D := by
  classical
  refine ⟨h.C_pos, h.D_pos, h.D_le_one, ?_⟩
  intro X hX
  have hsub :
      ((Finset.Icc 1 X).filter fun n => n ∉ T) ⊆
        ((Finset.Icc 1 X).filter fun n => n ∉ S) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, fun hnS => hn.2 (hST hnS)⟩
  have hcard : badCount T X ≤ badCount S X := by
    unfold badCount
    exact Finset.card_le_card hsub
  have hcardR : (badCount T X : ℝ) ≤ (badCount S X : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans (h.bad_bound X hX)
end PowerDense
end FirstPassageLinearTransport
