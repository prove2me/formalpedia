-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_standing_positive_discount_perpetual_cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:42:19.930176+00:00
-- url     : https://prove2.me/submissions/d6ed7f04-cc1c-4f96-bd12-c5cecc6d1b2a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) P := by
  obtain ⟨φ, hφ, hψ⟩ :=
    avram_wave4_05_source_positive_psi_root_of_standing X hX q hq
  exact avram_wave6_08_original_theta_perpetual_stieltjes_cash_integrable_q_ge_psi
    X x C D hD φ hφ q (le_of_eq hψ)
