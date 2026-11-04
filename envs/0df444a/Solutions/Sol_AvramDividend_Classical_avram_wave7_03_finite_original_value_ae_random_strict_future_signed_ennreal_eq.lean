-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_ae_random_strict_future_signed_ennreal_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:11:36.496405+00:00
-- url     : https://prove2.me/submissions/6f85d346-033e-4f90-a371-198a2fa4066a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact original strict-future signed Stieltjes cash and ENNReal
    Stieltjes cash agree almost surely under finite genuine dividendValue. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hFull :=
    avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
      X x D hD q hFinite
  filter_upwards [hFull] with ω hω
  have hInt :
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))
        (dividendMeasure D ω) :=
    hω.1.mono inter_subset_left le_rfl
  have hNonneg :
      0 ≤ᵐ[(dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))]
        (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall
      (fun t => (Real.exp_pos (-(q * t))).le)
  exact ofReal_integral_eq_lintegral_ofReal hInt hNonneg
