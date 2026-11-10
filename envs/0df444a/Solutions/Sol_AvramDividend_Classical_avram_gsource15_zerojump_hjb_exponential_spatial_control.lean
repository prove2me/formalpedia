-- Prove2me | solution 1 for AvramDividend.Classical.avram_gsource15_zerojump_hjb_exponential_spatial_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:42:44.03521+00:00
-- url     : https://prove2.me/submissions/a752e455-e40e-4811-ba34-a967fef83020

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_zerojump_hjb_linear_curvature_majorant
import Theorems.Thm_AvramDividend_Classical_avram_gsource15_exponential_derivative_comparison
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hw_nonneg : ∀ y ∈ Set.Icc a b, 0 ≤ w y)
    (hw_grad : ∀ y ∈ Set.Icc a b, 0 ≤ deriv w y)
    (hHJB : ∀ y ∈ Set.Icc a b, X.generator w y - q * w y ≤ 0)
    (hDer1 : ∀ y ∈ Set.Icc a b, HasDerivAt w (deriv w y) y)
    (hDer2 : ∀ y ∈ Set.Icc a b,
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y) :
    w b + deriv w b ≤
      Real.exp ((1 + 2 * (q + |X.c|) / X.σ ^ 2) * (b - a)) *
        (w a + deriv w a) := by
  let S : ℝ → ℝ := fun y => w y + deriv w y
  let K : ℝ := 2 * (q + |X.c|) / X.σ ^ 2
  have hSd (y : ℝ) (hy : y ∈ Set.Icc a b) :
      HasDerivAt S (deriv w y + iteratedDeriv 2 w y) y := by
    exact (hDer1 y hy).add (hDer2 y hy)
  have hSder : ∀ y ∈ Set.Icc a b, HasDerivAt S (deriv S y) y := by
    intro y hy
    have hd := hSd y hy
    rw [hd.deriv]
    exact hd
  have hSineq : ∀ y ∈ Set.Icc a b, deriv S y ≤ (1 + K) * S y := by
    intro y hy
    have hc := avram_gsource15_zerojump_hjb_linear_curvature_majorant
      X hν q hq w y hσ (hw_nonneg y hy) (hw_grad y hy) (hHJB y hy)
    rw [(hSd y hy).deriv]
    dsimp [S, K]
    nlinarith [hw_nonneg y hy]
  have hCmp := avram_gsource15_exponential_derivative_comparison
    S a b (1 + K) hab hSder hSineq
  dsimp [S, K] at hCmp
  exact hCmp
