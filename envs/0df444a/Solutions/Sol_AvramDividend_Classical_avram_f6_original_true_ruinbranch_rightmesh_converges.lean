-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_true_ruinbranch_rightmesh_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:20:37.759764+00:00
-- url     : https://prove2.me/submissions/cbc6a173-5b48-4b65-aaa1-626f02c24157

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_postpayment_reserve_rightmesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_eventually_below_strict_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ τ : ℝ≥0) (hστ : σ ≤ τ)
    (hτruin : (τ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let ρ : ℕ → ℝ≥0 := fun m =>
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
    let W : ℝ≥0 → ℝ := fun t =>
      if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    Tendsto (fun m => W (ρ m)) atTop (𝓝 (W σ)) := by
  dsimp only
  let ρ : ℕ → ℝ≥0 := fun m =>
    min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
  let f : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
  have hcont : Tendsto (fun m => f (ρ m)) atTop (𝓝 (f σ)) := by
    simpa only [f, ρ] using
      (avram_f6_original_true_postpayment_reserve_rightmesh_converges
        X x D hD (fun _ => τ) (fun _ _ => σ) (by intro k η; exact hστ)
        0 ω)
  change Tendsto (fun m : ℕ =>
    if ρ m = 0 ∨ (ρ m : ℝ≥0∞) < ruinTime X x D ω then
      f (ρ m) else riskProcess X x D (ρ m) ω)
      atTop (𝓝 (if σ = 0 ∨ (σ : ℝ≥0∞) <
        ruinTime X x D ω then f σ else riskProcess X x D σ ω))
  by_cases heq : σ = τ
  · have hρ (m : ℕ) : ρ m = σ := by
      dsimp [ρ]
      rw [heq]
      exact min_eq_left (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _))
    simpa only [hρ] using
      (tendsto_const_nhds (x := (if σ = 0 ∨ (σ : ℝ≥0∞) <
        ruinTime X x D ω then f σ else riskProcess X x D σ ω)))
  · have hstrict : σ < τ := lt_of_le_of_ne hστ heq
    have hσruin : (σ : ℝ≥0∞) < ruinTime X x D ω := by
      exact lt_of_lt_of_le (by exact ENNReal.coe_lt_coe.mpr hstrict) hτruin
    have hevent : ∀ᶠ m : ℕ in atTop,
        (ρ m : ℝ≥0∞) < ruinTime X x D ω := by
      have hh := avram_f6_original_rightmesh_eventually_below_strict_horizon
        σ τ hstrict
      filter_upwards [hh] with m hm
      exact lt_of_lt_of_le (by exact ENNReal.coe_lt_coe.mpr hm) hτruin
    have hw : (if σ = 0 ∨ (σ : ℝ≥0∞) < ruinTime X x D ω
        then f σ else riskProcess X x D σ ω) = f σ := by
      simp [hσruin]
    rw [hw]
    apply hcont.congr'
    filter_upwards [hevent] with m hm
    simp only [if_pos (Or.inr hm), f]
