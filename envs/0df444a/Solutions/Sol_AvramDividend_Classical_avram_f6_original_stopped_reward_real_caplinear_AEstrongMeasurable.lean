-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_stopped_reward_real_caplinear_AEstrongMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:25:35.090894+00:00
-- url     : https://prove2.me/submissions/e1dcc18a-1ad0-4ecd-a29c-618081b79c75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section


theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) 
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, AEStronglyMeasurable (fun ω =>
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by
  intro k
  have hId :=
    avram_f6_original_stopped_reward_real_caplinear_cash_exact
      X x C hC hxc w D hD q σ F hFsource
  have hFun : (fun ω =>
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z
        else if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)
      let W : ℝ := if σ k ω = 0 ∨
          (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
        else riskProcess X x D (σ k ω) ω
      Real.exp (-(q * (σ k ω : ℝ))) * V W +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) = F k := by
    funext ω
    simpa only using (hId k ω).symm
  rw [hFun]
  exact (hFI k).aestronglyMeasurable
