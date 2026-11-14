-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a177_original_gaussian_true_stopped_source_real_energy_lintegral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:42:44.785207+00:00
-- url     : https://prove2.me/submissions/88b4a08a-256d-44fb-b132-a63710b15f21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a39_original_stopped_uniform_second_energy_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian stopped-prefix centred real squared-energy sum
inherits the Proved original source extended nonnegative energy estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ < ρ ω then
          (X.X ((i : ℝ≥0) * Δ + Δ) ω -
            X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c)^2
        else 0
    ∀ m : ℕ,
      (∫⁻ ω, ENNReal.ofReal (E m ω) ∂P) ≤
        ENNReal.ofReal ((n : ℝ) * X.σ^2) := by
  classical
  intro E m
  let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    X.X ((i : ℝ≥0) * Δ m + Δ m) ω -
      X.X ((i : ℝ≥0) * Δ m) ω - (Δ m : ℝ) * X.c
  have hWidth (m : ℕ) :
      (Δ m : ℝ) = (n : ℝ) / ((m : ℝ) + 1) := by
    simp only [Δ, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one]
  have hZm (m i : ℕ) : Measurable (Z m i) := by
    have h1 : Measurable (X.X ((i : ℝ≥0) * Δ m + Δ m)) :=
      (X.adapted ((i : ℝ≥0) * Δ m + Δ m)).mono (𝓕.le _) le_rfl
    have h0 : Measurable (X.X ((i : ℝ≥0) * Δ m)) :=
      (X.adapted ((i : ℝ≥0) * Δ m)).mono (𝓕.le _) le_rfl
    exact (h1.sub h0).sub measurable_const
  have hEq (ω : Ω) :
      ENNReal.ofReal (E m ω) =
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal ((Z m i ω)^2) else 0 := by
    change ENNReal.ofReal (∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ m < ρ ω then (Z m i ω)^2 else 0) = _
    rw [ENNReal.ofReal_sum_of_nonneg (by
      intro i hi
      by_cases hActive : (i : ℝ≥0) * Δ m < ρ ω
      · simpa only [if_pos hActive] using sq_nonneg (Z m i ω)
      · simp [hActive])]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  have hSource := avram_ga_a39_original_stopped_uniform_second_energy_bound
    X hNuZero n Δ hWidth ρ (fun m i hi => hZm m i) m
  calc
    (∫⁻ ω, ENNReal.ofReal (E m ω) ∂P) =
      (∫⁻ ω, ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ m < ρ ω then
          ENNReal.ofReal ((Z m i ω)^2) else 0 ∂P) :=
      lintegral_congr hEq
    _ ≤ _ := hSource
