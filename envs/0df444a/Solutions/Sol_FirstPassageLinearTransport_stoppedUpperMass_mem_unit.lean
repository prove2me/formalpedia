-- Prove2me | solution 1 for FirstPassageLinearTransport.stoppedUpperMass_mem_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:22.862481+00:00
-- url     : https://prove2.me/submissions/7571892f-0965-4c90-99e2-5537224acd74

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_nonneg
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_le_one
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, 0 ≤ stoppedUpperMass p x lo hi r z ∧
      stoppedUpperMass p x lo hi r z ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : hi ≤ z <;> simp [stoppedUpperMass, hz]
  | succ r ihr =>
      intro z
      by_cases hup : hi ≤ z
      · simp [stoppedUpperMass, hup]
      · by_cases hlo : z < lo
        · simp [stoppedUpperMass, hup, hlo]
        · simp only [stoppedUpperMass, hup, hlo, if_false]
          exact ⟨bernoulliAverage_nonneg hp₀ hp₁ (ihr _).1 (ihr _).1,
            bernoulliAverage_le_one hp₀ hp₁ (ihr _).2 (ihr _).2⟩
end FirstPassageLinearTransport
