-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerSurvivalMass_le_stopped_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:43.22719+00:00
-- url     : https://prove2.me/submissions/79edbc25-3145-4803-8727-f032c425888e

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_bernoulliAverage_mono
import Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_mem_unit
import Theorems.Thm_FirstPassageLinearTransport_stoppedUpperMass_mem_unit
import Theorems.Thm_FirstPassageLinearTransport_stoppedHorizonMass_mem_unit
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
    ∀ r z, lowerSurvivalMass p x lo r z ≤
      stoppedUpperMass p x lo hi r z + stoppedHorizonMass p x lo hi r z := by
  intro r
  induction r with
  | zero =>
      intro z
      by_cases hlo : lo ≤ z
      · by_cases hup : hi ≤ z
        · simp [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass, hlo, hup]
        · have hnotstop : ¬(z < lo ∨ hi ≤ z) :=
            not_or_intro (not_lt.mpr hlo) hup
          simp [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass,
            hlo, hup, not_lt.mpr hlo, hnotstop]
      · have hlt : z < lo := lt_of_not_ge hlo
        have hupNonneg := (stoppedUpperMass_mem_unit hp₀ hp₁ x lo hi 0 z).1
        simp only [lowerSurvivalMass, hlo, if_false]
        exact add_nonneg hupNonneg
          (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi 0 z).1
  | succ r ihr =>
      intro z
      by_cases hlo : lo ≤ z
      · by_cases hup : hi ≤ z
        · have hsurv' :=
            (lowerSurvivalMass_mem_unit hp₀ hp₁ x lo (r + 1) z).2
          have hhor :=
            (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
          rw [stoppedUpperMass]
          simp only [hup, if_true]
          linarith
        · have hnotlo : ¬z < lo := not_lt.mpr hlo
          have hnotstop : ¬(z < lo ∨ hi ≤ z) := not_or_intro hnotlo hup
          have hf := ihr (z + x false)
          have ht := ihr (z + x true)
          simp only [lowerSurvivalMass, stoppedUpperMass, stoppedHorizonMass,
            hlo, hup, hnotlo, hnotstop, if_true, if_false]
          calc
            bernoulliAverage p
                (lowerSurvivalMass p x lo r (z + x false))
                (lowerSurvivalMass p x lo r (z + x true)) ≤
              bernoulliAverage p
                (stoppedUpperMass p x lo hi r (z + x false) +
                  stoppedHorizonMass p x lo hi r (z + x false))
                (stoppedUpperMass p x lo hi r (z + x true) +
                  stoppedHorizonMass p x lo hi r (z + x true)) :=
                bernoulliAverage_mono hp₀ hp₁ hf ht
            _ = bernoulliAverage p
                  (stoppedUpperMass p x lo hi r (z + x false))
                  (stoppedUpperMass p x lo hi r (z + x true)) +
                bernoulliAverage p
                  (stoppedHorizonMass p x lo hi r (z + x false))
                  (stoppedHorizonMass p x lo hi r (z + x true)) := by
              unfold bernoulliAverage
              ring
      · have hlt : z < lo := lt_of_not_ge hlo
        have hupNonneg :=
          (stoppedUpperMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
        have hhorNonneg :=
          (stoppedHorizonMass_mem_unit hp₀ hp₁ x lo hi (r + 1) z).1
        simp only [lowerSurvivalMass, hlo, if_false]
        exact add_nonneg hupNonneg hhorNonneg
end FirstPassageLinearTransport
