-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_source_centered_component_unique_of_equal_jump_totals
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:41:48.212353+00:00
-- url     : https://prove2.me/submissions/8c983d49-f12b-4d67-803d-4761a7082e02

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The centred continuous Gaussian source component is unique a.s. on the
original sample space whenever two original Levy-Ito representations agree on
their total jump component, regardless of the small/large split. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y Z : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hZν : Z.ν = 0)
    (hYσ : Y.σ = X.σ) (hZσ : Z.σ = X.σ)
    (Jsmall₁ Jlarge₁ Jsmall₂ Jlarge₂ : ℝ≥0 → Ω → ℝ)
    (hSource₁ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall₁ u ω + Jlarge₁ u ω)
    (hSource₂ : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Z.X u ω - (u : ℝ) * Z.c) + Jsmall₂ u ω + Jlarge₂ u ω)
    (hJumpTotal : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Jsmall₁ u ω + Jlarge₁ u ω =
        Jsmall₂ u ω + Jlarge₂ u ω) :
    ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Y.X u ω - (u : ℝ) * Y.c =
        Z.X u ω - (u : ℝ) * Z.c := by
  filter_upwards [hSource₁, hSource₂, hJumpTotal] with ω h₁ h₂ hj
  intro u
  have e₁ := h₁ u
  have e₂ := h₂ u
  have ej := hj u
  linarith
