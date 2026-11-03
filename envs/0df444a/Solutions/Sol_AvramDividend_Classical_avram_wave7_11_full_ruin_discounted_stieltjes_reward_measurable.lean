-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_full_ruin_discounted_stieltjes_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:10:17.827719+00:00
-- url     : https://prove2.me/submissions/4ee5063f-1346-47d7-a57f-cfbb39c70228

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The complete finite-horizon reward up to ruin is measurable for the
    original Lévy process and original Stieltjes dividend strategy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have heq : (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (fun ω : Ω => ⨆ n : ℕ,
        ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    funext ω
    exact avram_wave7_11_ruin_clock_truncation_inner_lintegral_iSup
      D ω (ruinTime X x D ω) q T
  rw [heq]
  exact Measurable.iSup fun n =>
    avram_wave5_05_original_arbitrary_measurable_stop_complete_stieltjes_reward_measurable
      X x D hD q T (fun _ : Ω => (n : ℝ≥0∞)) measurable_const
