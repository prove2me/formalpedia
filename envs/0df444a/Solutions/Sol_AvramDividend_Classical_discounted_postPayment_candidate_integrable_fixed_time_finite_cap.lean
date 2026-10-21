-- Prove2me | solution 1 for AvramDividend.Classical.discounted_postPayment_candidate_integrable_fixed_time_finite_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T08:57:08.596139+00:00
-- url     : https://prove2.me/submissions/9046f03f-63f2-4a0b-b543-ce43aa38e445

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_bounded_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (t : ℝ≥0) :
    Integrable (fun ω =>
      Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hwAdapt : Adapted 𝓕.rightCont
      (fun s ω => w (x + X.X s ω - rightLimit D s ω)) :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD.1.1 w hw_cont hw_neg).2
  have hwMeas : Measurable
      (fun ω => w (x + X.X t ω - rightLimit D t ω)) :=
    (hwAdapt t).mono ((𝓕.rightCont).le t) le_rfl
  have hfMeas : Measurable
      (fun ω => Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)) :=
    measurable_const.mul hwMeas
  obtain ⟨B, hB0, hB⟩ :=
    discounted_postPayment_candidate_bounded_finite_cap
      X q hq w x c hc D hD hxc
      hw_cont hw0 hw_neg hw_smooth hw_hjb
  apply Integrable.of_mem_Icc 0 B hfMeas.aemeasurable
  filter_upwards [] with ω
  exact hB ω t
