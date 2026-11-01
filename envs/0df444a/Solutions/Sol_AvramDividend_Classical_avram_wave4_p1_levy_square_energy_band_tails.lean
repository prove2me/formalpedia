-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_levy_square_energy_band_tails
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:18:05.415855+00:00
-- url     : https://prove2.me/submissions/a4857da1-418d-4a3b-abc5-ae4e475d9dba

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (g : E → ℝ≥0∞)
    (hg : Measurable g) (henergy : ∫⁻ z, g z ∂ν < ∞)
    (B : ℕ → Set E)
    (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, ν (B n) < ∞)
    (hBmono : Monotone B)
    (hBcover : (⋃ n, B n) = Set.univ) :
    Tendsto (fun n : ℕ => ∫⁻ z in (B n)ᶜ, g z ∂ν)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by
  let ρ : Measure E := ν.withDensity g
  have hρtotal : ρ Set.univ < ∞ := by
    change ν.withDensity g Set.univ < ∞
    rw [withDensity_apply g MeasurableSet.univ]
    simpa only [Measure.restrict_univ] using henergy
  have hρfinite : ∃ n : ℕ, ρ ((B n)ᶜ) ≠ ∞ := by
    refine ⟨0, ne_of_lt ?_⟩
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) hρtotal
  have hanti : Antitone (fun n : ℕ => (B n)ᶜ) := by
    intro i j hij
    exact Set.compl_subset_compl.mpr (hBmono hij)
  have hlim :=
    tendsto_measure_iInter_atTop
      (μ := ρ) (s := fun n : ℕ => (B n)ᶜ)
      (fun n => (hB n).compl.nullMeasurableSet) hanti hρfinite
  have hiInter : (⋂ n : ℕ, (B n)ᶜ) = (∅ : Set E) := by
    rw [← Set.compl_iUnion, hBcover]
    simp
  have hfun :
      (ρ ∘ fun n : ℕ => (B n)ᶜ) =
        (fun n : ℕ => ∫⁻ z in (B n)ᶜ, g z ∂ν) := by
    funext n
    exact withDensity_apply g (hB n).compl
  rw [hfun, hiInter, measure_empty] at hlim
  exact hlim
