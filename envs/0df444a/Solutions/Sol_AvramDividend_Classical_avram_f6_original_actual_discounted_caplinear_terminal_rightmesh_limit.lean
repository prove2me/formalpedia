-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_actual_discounted_caplinear_terminal_rightmesh_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:30:05.468227+00:00
-- url     : https://prove2.me/submissions/5871c1ae-1bbc-473c-a0c0-531f204cde7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_rightmesh_converges
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_caplinear_discounted_terminal_continuous_limit
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_rightmesh_eventually_below_strict_horizon
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_delayed_clock_real_min_tends_to_stopped
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_preruin_actual_postpayment_solvency
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
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ω : Ω) (σ τ : ℝ≥0)
    (hστ : σ ≤ τ) (hτruin : (τ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let ρ : ℕ → ℝ≥0 := fun m =>
      min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
    let W : ℝ≥0 → ℝ := fun t =>
      if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let V : ℝ → ℝ := fun z =>
      if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)
    Tendsto (fun m => Real.exp (-(q * (ρ m : ℝ))) * V (W (ρ m)))
      atTop (𝓝 (Real.exp (-(q * (σ : ℝ))) * V (W σ))) := by
  dsimp only
  let ρ : ℕ → ℝ≥0 := fun m =>
    min τ (σ + (1 : ℝ≥0) / ((m : ℝ≥0) + 1))
  let W : ℝ≥0 → ℝ := fun t =>
    if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X t ω - rightLimit D t ω
    else riskProcess X x D t ω
  let V : ℝ → ℝ := fun z =>
    if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
  change Tendsto (fun m => Real.exp (-(q * (ρ m : ℝ))) * V (W (ρ m)))
    atTop (𝓝 (Real.exp (-(q * (σ : ℝ))) * V (W σ)))
  by_cases heq : σ = τ
  · subst τ
    have hρ (m : ℕ) : ρ m = σ := by
      dsimp [ρ]
      exact min_eq_left (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _))
    simp only [hρ]
    exact tendsto_const_nhds
  · have hstrict : σ < τ := lt_of_le_of_ne hστ heq
    have hsruin : (σ : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hstrict) hτruin
    have hclock : Tendsto ρ atTop (𝓝 σ) := by
      apply NNReal.tendsto_coe.mp
      simpa only [ρ, NNReal.coe_min, NNReal.coe_add, NNReal.coe_div,
        NNReal.coe_one, NNReal.coe_natCast] using
        avram_f6_original_delayed_clock_real_min_tends_to_stopped
          σ τ hστ
    have hWconv : Tendsto (fun m => W (ρ m)) atTop (𝓝 (W σ)) := by
      simpa only [W, ρ] using
        (avram_f6_original_true_ruinbranch_rightmesh_converges
          X x D hD.1.1 ω σ τ hστ hτruin)
    have hpoint (t : ℝ≥0) : (t : ℝ) ∈ Icc (0 : ℝ) (t : ℝ) :=
      ⟨by exact_mod_cast t.property, le_rfl⟩
    have hsolv (t : ℝ≥0)
        (ht : (t : ℝ≥0∞) < ruinTime X x D ω) :
        0 ≤ x + X.X t ω - rightLimit D t ω := by
      simpa using
        (avram_wave5_04b_closed_preruin_actual_postpayment_solvency
          X x C D hD ω t (Or.inr ht) (t : ℝ) (hpoint t))
    have hWσ : 0 ≤ W σ := by
      simpa only [W, if_pos (Or.inr hsruin)] using hsolv σ hsruin
    have hevent : ∀ᶠ m : ℕ in atTop,
        (ρ m : ℝ≥0∞) < ruinTime X x D ω := by
      have hh := avram_f6_original_rightmesh_eventually_below_strict_horizon
        σ τ hstrict
      filter_upwards [hh] with m hm
      exact lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hm) hτruin
    have hWpos : ∀ᶠ m : ℕ in atTop, 0 ≤ W (ρ m) := by
      filter_upwards [hevent] with m hm
      simpa only [W, if_pos (Or.inr hm)] using hsolv (ρ m) hm
    simpa only [V] using
      (avram_f6_original_caplinear_discounted_terminal_continuous_limit
        w hw_cont C q ρ σ hclock (fun m => W (ρ m)) (W σ)
        hWconv hWσ hWpos)
