-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward23_original_normalised_stopped_reward_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:28:39.422191+00:00
-- url     : https://prove2.me/submissions/beecf23d-fa8a-4441-ac0c-d719b06c279b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_any_clock_paid_reward_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_masked_reward_dominates_exact_F
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y < 0, w y = 0)
    (hwSmooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (σ : Ω → ℝ≥0) :
    ∀ ω, 0 ≤
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (if (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
            else riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal  := by
  intro ω
  let F : ℕ → Ω → ℝ := fun _ η =>
    Real.exp (-(q * (σ η : ℝ))) *
      w (if σ η = 0 ∨ (σ η : ℝ≥0∞) < ruinTime X x D η then
        x + X.X (σ η) η - rightLimit D (σ η) η
        else riskProcess X x D (σ η) η) +
    (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (σ η : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D η)).toReal
  have hFsource : ∀ k η, F k η =
      Real.exp (-(q * (σ η : ℝ))) *
        w (if σ η = 0 ∨ (σ η : ℝ≥0∞) < ruinTime X x D η then
          x + X.X (σ η) η - rightLimit D (σ η) η
          else riskProcess X x D (σ η) η) +
      (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (σ η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D η)).toReal := by
    intro k η
    rfl
  have hFnonneg : 0 ≤ F 0 ω := by
    simpa only [F] using
      (avram_f6_original_any_clock_paid_reward_nonnegative
        X hBV w C hC hw0 hwCont hwNeg hwSmooth hwGrad
        x hxc D hD q σ ω)
  have hFle : F 0 ω ≤ (if σ ω = 0 then w x else F 0 ω) :=
    avram_ubv_loc6_original_masked_reward_dominates_exact_F
      X x q w C D hD hjump (fun _ => σ) F
      (by intro k η; exact hFsource k η) 0 ω
  have hG := le_trans hFnonneg hFle
  by_cases hσ : σ ω = 0
  · simpa only [hσ, if_true] using hG
  · simpa [hσ, F] using hG
