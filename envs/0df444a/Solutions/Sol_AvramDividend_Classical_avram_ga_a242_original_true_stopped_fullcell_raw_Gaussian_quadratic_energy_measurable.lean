-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:21:05.482984+00:00
-- url     : https://prove2.me/submissions/5e5bf4e8-56a4-4699-bbe7-3034961d273c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    ∀ m : ℕ, Measurable (fun ω : Ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω ∧ s + Δ ≤ ρ ω
        then R^2 else 0) := by
  intro m
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  have hρ : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  apply Finset.measurable_sum
  intro i hi
  have h0 : Measurable (X.X (s i)) :=
    (X.adapted (s i)).mono (𝓕.le _) le_rfl
  have h1 : Measurable (X.X (s i+Δ)) :=
    (X.adapted (s i+Δ)).mono (𝓕.le _) le_rfl
  have hMask : MeasurableSet
      {ω : Ω | s i < ρ ω ∧ s i + Δ ≤ ρ ω} := by
    have hStart : MeasurableSet {ω : Ω | s i < ρ ω} :=
      (show MeasurableSet (Set.Ioi (s i) : Set ℝ≥0)
        from measurableSet_Ioi).preimage hρ
    have hEnd : MeasurableSet {ω : Ω | s i+Δ ≤ ρ ω} :=
      (show MeasurableSet (Set.Ici (s i+Δ) : Set ℝ≥0)
        from measurableSet_Ici).preimage hρ
    exact hStart.inter hEnd
  exact Measurable.ite hMask ((h1.sub h0).pow_const 2) measurable_const
