-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a176_original_gaussian_stopped_prefix_centered_square_measurable_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:52:26.813952+00:00
-- url     : https://prove2.me/submissions/4d7ba77d-9950-4d2a-9777-63bd9e73953d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original adapted Gaussian increments and the true stopped prefix mask
give a measurable nonnegative centred-square physical grid energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        if (i : ℝ≥0) * Δ < ρ ω then
          (X.X ((i : ℝ≥0) * Δ + Δ) ω -
            X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c)^2
        else 0
    ∀ m : ℕ, Measurable (E m) ∧ ∀ ω : Ω, 0 ≤ E m ω := by
  classical
  intro E m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  have hρm : Measurable (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    (hρstop.measurable).mono hρstop.measurableSpace_le le_rfl
  have hMask (i : ℕ) :
      MeasurableSet {ω : Ω | (i : ℝ≥0) * Δ < ρ ω} := by
    have h : MeasurableSet
        {ω : Ω | (((i : ℝ≥0) * Δ : ℝ≥0) : WithTop ℝ≥0) <
          (ρ ω : WithTop ℝ≥0)} :=
      measurableSet_Ioi.preimage hρm
    simpa only [WithTop.coe_lt_coe] using h
  have hZ (i : ℕ) : Measurable (fun ω =>
      X.X ((i : ℝ≥0) * Δ + Δ) ω -
        X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c) := by
    have h1 : Measurable (X.X ((i : ℝ≥0) * Δ + Δ)) :=
      (X.adapted ((i : ℝ≥0) * Δ + Δ)).mono (𝓕.le _) le_rfl
    have h0 : Measurable (X.X ((i : ℝ≥0) * Δ)) :=
      (X.adapted ((i : ℝ≥0) * Δ)).mono (𝓕.le _) le_rfl
    exact (h1.sub h0).sub measurable_const
  constructor
  · dsimp [E]
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite (hMask i) ((hZ i).pow_const 2) measurable_const
  · intro ω
    change 0 ≤ ∑ i ∈ Finset.range m,
      if (i : ℝ≥0) * Δ < ρ ω then
        (X.X ((i : ℝ≥0) * Δ + Δ) ω -
          X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c)^2
      else 0
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
