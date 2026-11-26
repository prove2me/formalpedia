-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerSurvivalMass_mem_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:30:19.822188+00:00
-- url     : https://prove2.me/submissions/87580947-8a58-4126-9e90-cd2097c38072

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
    (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, 0 ≤ lowerSurvivalMass p x lo r z ∧
      lowerSurvivalMass p x lo r z ≤ 1 := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hz : lo ≤ z <;> simp [lowerSurvivalMass, hz]
  | succ r ihr =>
      intro z
      by_cases hz : lo ≤ z
      · simp only [lowerSurvivalMass, hz, if_true]
        exact ⟨bernoulliAverage_nonneg hp₀ hp₁ (ihr _).1 (ihr _).1,
          bernoulliAverage_le_one hp₀ hp₁ (ihr _).2 (ihr _).2⟩
      · simp [lowerSurvivalMass, hz]
end FirstPassageLinearTransport
