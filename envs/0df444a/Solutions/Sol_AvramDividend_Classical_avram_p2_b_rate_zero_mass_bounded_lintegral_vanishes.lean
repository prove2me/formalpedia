-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_zero_mass_bounded_lintegral_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:57.417908+00:00
-- url     : https://prove2.me/submissions/3f43d678-9f49-4836-a554-9aaca98c8577

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    (μ : ℝ → Measure ℝ) (g : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : C ≠ ⊤) (hgbound : ∀ z : ℝ, g z ≤ C)
    (hmass : Tendsto (fun h : ℝ => μ h Set.univ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞))) :
    Tendsto (fun h : ℝ => ∫⁻ z : ℝ, g z ∂(μ h))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
  have hlim : Tendsto (fun h : ℝ => C * μ h Set.univ)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (0 : ℝ≥0∞)) := by
    simpa using (ENNReal.Tendsto.const_mul hmass (Or.inr hC))
  have hupper (h : ℝ) :
      (∫⁻ z : ℝ, g z ∂(μ h)) ≤ C * μ h Set.univ := by
    calc
      (∫⁻ z : ℝ, g z ∂(μ h)) ≤ (∫⁻ _ : ℝ, C ∂(μ h)) :=
        lintegral_mono (fun z => hgbound z)
      _ = C * μ h Set.univ := by simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hlim (fun _ => bot_le) hupper
