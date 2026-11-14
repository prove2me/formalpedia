-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a169_original_true_fullcell_gaussian_raw_centered_square_cross_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:16:17.684564+00:00
-- url     : https://prove2.me/submissions/2490ca68-f421-4c23-8c5d-5d615eb9cf6d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real physical source cross energy: prefix L1 plus source submask
measurable dominance yields full-cell integrability and L1 vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω then |R^2 - Z^2| else 0
    (∀ m : ℕ, Integrable (Cross m) P) ∧
    Tendsto (fun m : ℕ => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  exact avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
    X hNuZero n ρ hρstop
