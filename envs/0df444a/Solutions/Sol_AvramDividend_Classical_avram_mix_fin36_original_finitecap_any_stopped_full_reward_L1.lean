-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:39:24.470961+00:00
-- url     : https://prove2.me/submissions/f9242e36-9795-4baa-854c-d7ca3152817d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_F_family_integrable_from_exact_cash
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (G : Ω → ℝ)
    (hGsource : ∀ ω, G ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨
              (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    Integrable G P := by
  classical
  have hρmeas : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hρReal : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    hρmeas.coe_nnreal_real
  have hCashI :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q ρ (n : ℝ≥0) hρReal hρbound
  have hGmeas : Measurable G :=
    avram_ubv_top9_original_any_clock_source_reward_measurable
      X x q w hw_cont hw_neg D hD.1.1 ρ hρstop G hGsource
  have hFamSource :
      ∀ k ω, (fun _ : ℕ => G) k ω =
        Real.exp (-(q * ((fun _ : ℕ => ρ) k ω : ℝ))) *
          w (if (fun _ : ℕ => ρ) k ω = 0 ∨
                ((fun _ : ℕ => ρ) k ω : ℝ≥0∞) < ruinTime X x D ω then
              x + X.X ((fun _ : ℕ => ρ) k ω) ω -
                rightLimit D ((fun _ : ℕ => ρ) k ω) ω
            else riskProcess X x D ((fun _ : ℕ => ρ) k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Iic ((fun _ : ℕ => ρ) k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
    intro k ω
    exact hGsource ω
  have hFamI :=
    avram_ubv_finite9_original_F_family_integrable_from_exact_cash
      X x q hq C hCfinite hxc w hw_cont hw_neg D hD
      ρ hCashI (fun _ : ℕ => ρ) (by intro k ω; rfl)
      (fun _ : ℕ => G) hFamSource
      (by intro k; exact hGmeas.aestronglyMeasurable)
  exact hFamI 0
