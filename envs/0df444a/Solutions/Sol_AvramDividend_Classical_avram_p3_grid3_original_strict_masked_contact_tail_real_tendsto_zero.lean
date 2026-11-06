-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_original_strict_masked_contact_tail_real_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:13:44.942562+00:00
-- url     : https://prove2.me/submissions/e03ed037-a284-44ed-a63b-d45251b7a853

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The strict original stopped contact-tail vanishes after conversion to real cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal)
      atTop (𝓝 (0 : ℝ)) := by
  have hENN :=
    avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
      X x D hD ω q hq T τ hτT δ hδpos hδanti hδ
  have hCont : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
    ENNReal.continuousAt_toReal (by simp)
  simpa only [Function.comp_def, ENNReal.toReal_zero]
    using hCont.tendsto.comp hENN
