-- Prove2me | solution 1 for AvramDividend.Classical.avram_j18_original_bounded_band_rightcont_optional_sampling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T21:34:14.638204+00:00
-- url     : https://prove2.me/submissions/07300be9-2346-404c-ba42-8357a2be361e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_finite_range_optional_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja18_integrable_of_dom_ae_grid_limit
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_rightcont_upper_grid_stops
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Assemble exact original-filtration finite-clock optional sampling,
source right-continuity and uniformly dominated conditional limits. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (Jsmall : ℝ≥0 → Ω → ℝ) (B : Ω → ℝ)
    (hInt : ∀ t : ℝ≥0, Integrable (Jsmall t) P)
    (hMart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => Jsmall u ω) (Set.Ici t) t)
    (hZero : ∀ᵐ ω ∂P, Jsmall 0 ω = 0)
    (hBInt : Integrable B P)
    (hDom : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) →
      ‖Jsmall t ω‖ ≤ B ω) :
    Integrable (fun ω => Jsmall (τ ω) ω) P ∧
    (∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun ω => Jsmall (τ ω) ω) ω = 0) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨ρ, hStop, hRange, hAbove, hBelow, hTimeConv⟩ :=
    avram_ja18_original_rightcont_upper_grid_stops τ hτstop n hτbound
  let V : ℕ → Ω → ℝ := fun k ω => Jsmall (ρ k ω) ω
  have hGrid (k : ℕ) :
      Integrable (V k) P ∧
      (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P (V k) ω = 0) := by
    obtain ⟨S, hS⟩ := hRange k
    exact avram_ja18_finite_range_optional_condexp_zero
      Jsmall (ρ k) (n : ℝ≥0) (hStop k) (hBelow k)
      S hS hInt hMart hZero
  have hVInt : ∀ k, Integrable (V k) P := fun k => (hGrid k).1
  have hVZero : ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (V k) ω = 0 :=
    fun k => (hGrid k).2
  have hValueConv : ∀ᵐ ω ∂P,
      Tendsto (fun k => V k ω) atTop (𝓝 (Jsmall (τ ω) ω)) :=
    avram_ja18_rightcontinuous_clock_composition
      Jsmall τ ρ hRight hAbove hTimeConv
  have hVDom : ∀ k, ∀ᵐ ω ∂P, ‖V k ω‖ ≤ B ω := by
    intro k
    filter_upwards [hDom] with ω hw
    exact hw (ρ k ω) (hBelow k ω)
  have hLimitDom : ∀ᵐ ω ∂P, ‖Jsmall (τ ω) ω‖ ≤ B ω := by
    filter_upwards [hDom] with ω hw
    exact hw (τ ω) (hτbound ω)
  exact ⟨avram_ja18_integrable_of_dom_ae_grid_limit
      V (fun ω => Jsmall (τ ω) ω) B hVInt hValueConv hBInt hLimitDom,
    avram_ja18_original_dominated_condExp_zero_limit
      V (fun ω => Jsmall (τ ω) ω) B hVInt hValueConv hBInt hVDom hVZero⟩
