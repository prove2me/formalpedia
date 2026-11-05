-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep15_localised_positive_mesh_mean_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:26:29.389321+00:00
-- url     : https://prove2.me/submissions/d2889ae8-e389-4086-b9c1-c11b84b32add

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : ℕ → Ω → ℝ) (B : Ω → ℝ)
    (hE : ∀ n, Integrable (E n) P)
    (hB : Integrable B P)
    (hE_nonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ E n ω)
    (hB_nonneg : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hSmall : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∀ᵐ ω ∂P, E n ω ≤ ε * B ω) :
    Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (nhds 0) := by
  have hBmean : 0 ≤ ∫ ω, B ω ∂P :=
    integral_nonneg_of_ae hB_nonneg
  have hEmean (n : ℕ) : 0 ≤ ∫ ω, E n ω ∂P :=
    integral_nonneg_of_ae (hE_nonneg n)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun n => lt_of_lt_of_le ha (hEmean n))
  · intro a ha
    let ε : ℝ := a / ((∫ ω, B ω ∂P) + 1)
    have hDen : 0 < ((∫ ω, B ω ∂P) + 1) := by linarith
    have hε : 0 < ε := div_pos ha hDen
    have hεEq : ε * ((∫ ω, B ω ∂P) + 1) = a := by
      dsimp [ε]
      field_simp [ne_of_gt hDen]
    filter_upwards [hSmall ε hε] with n hn
    have hMeanBound : (∫ ω, E n ω ∂P) ≤
        ε * (∫ ω, B ω ∂P) := by
      calc
        _ ≤ (∫ ω, ε * B ω ∂P) :=
          integral_mono_ae (hE n) (hB.const_mul ε) hn
        _ = ε * (∫ ω, B ω ∂P) := by simp only [integral_const_mul]
    linarith only [hMeanBound, hεEq, hε]
