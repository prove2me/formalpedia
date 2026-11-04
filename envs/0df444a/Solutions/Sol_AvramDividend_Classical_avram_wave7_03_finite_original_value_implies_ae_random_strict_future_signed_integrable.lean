-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_finite_original_value_implies_ae_random_strict_future_signed_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:11:33.874802+00:00
-- url     : https://prove2.me/submissions/ebabaa53-8a45-4291-afa0-5fae51b39ded

import Mathlib.MeasureTheory.Integral.IntegrableOn
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

/-- Finite original expected dividend value supplies real integrability
    of the exact strict-future Stieltjes cash at every path-dependent clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (q : ℝ)
    (T : Ω → ℝ)
    (hFinite : dividendValue X q x D < ⊤) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω))
        (dividendMeasure D ω) := by
  have hFull :=
    avram_wave7_03_finite_value_implies_original_unrestricted_signed_stieltjes_integrable_ae
      X x D hD q hFinite
  filter_upwards [hFull] with ω hω
  exact hω.1.mono inter_subset_left le_rfl
