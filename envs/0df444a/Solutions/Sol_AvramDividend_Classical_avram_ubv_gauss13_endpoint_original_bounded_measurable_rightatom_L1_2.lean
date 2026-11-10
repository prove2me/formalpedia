-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_bounded_measurable_rightatom_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:59:37.012369+00:00
-- url     : https://prove2.me/submissions/93d1b97a-3552-4736-872b-62419dc4537d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσmeas : Measurable (fun ω : Ω => (σ ω : ℝ)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (σ ω : ℝ))) *
          (rightLimit D (σ ω) ω - D (σ ω) ω)
      else 0) P := by
  have hclosed :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q σ T hσmeas hσbound
  have hstrict :=
    avram_ubv_gauss13_endpoint_original_bounded_measurable_strict_cash_L1
      X x C D hD q hq σ hσmeas T hσbound
  convert hclosed.sub hstrict using 1
  funext ω
  have hcash :=
    avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
      X x C D hD ω q hq (σ ω)
  dsimp only [Pi.sub_apply]
  linarith
