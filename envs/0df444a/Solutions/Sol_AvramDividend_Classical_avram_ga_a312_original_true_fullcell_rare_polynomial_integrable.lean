-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:29:13.023725+00:00
-- url     : https://prove2.me/submissions/bcdd661d-488e-47d2-8d72-e31125e14384

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let Poly : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0
    ∀ m, Integrable (Poly m) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro Δ s R Z Poly
  let A : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω ∧ s m i+Δ m ≤ ρ ω
  have hρ : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hRm (m i : ℕ) : Measurable (R m i) := by
    have h0 : Measurable (X.X (s m i)) :=
      (X.adapted (s m i)).mono (𝓕.le _) le_rfl
    have h1 : Measurable (X.X (s m i+Δ m)) :=
      (X.adapted (s m i+Δ m)).mono (𝓕.le _) le_rfl
    exact h1.sub h0
  have hAm (m i : ℕ) : MeasurableSet {ω : Ω | A m i ω} := by
    have hStart : MeasurableSet {ω : Ω | s m i < ρ ω} :=
      (show MeasurableSet (Set.Ioi (s m i) : Set ℝ≥0)
        from measurableSet_Ioi).preimage hρ
    have hEnd : MeasurableSet {ω : Ω | s m i+Δ m ≤ ρ ω} :=
      (show MeasurableSet (Set.Ici (s m i+Δ m) : Set ℝ≥0)
        from measurableSet_Ici).preimage hρ
    exact hStart.inter hEnd
  have hRawI := avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
    X hν n ρ hρstop
  have hG := avram_ga_a311_masked_Gaussian_polynomial_finite_mesh_integrable_from_raw_square
    P R (fun m => (Δ m : ℝ)*X.c) A δ hδ hRm hAm
    (by simpa only [R,A,s,Δ] using hRawI)
  exact hG
