-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_either_future_clock_source_ubv_value_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:48:47.181402+00:00
-- url     : https://prove2.me/submissions/b1a0de6c-9baa-410f-b81f-e13a75f58868

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
import Mathlib.Data.Real.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T)
    (hEitherClock : 0 < x →
      (∃ n : ℕ, T < (n : ℝ) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) ∨
      (∃ η : Ω → ℝ≥0∞,
        (∀ᵐ ω ∂P, ENNReal.ofReal T < η ω) ∧
        (∫⁻ ω, ∫⁻ t in paymentTimes
          (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  apply avram_wave7_11_minimal_original_ubv_ae_clock_value_bridge
    X hBV q w C hw0 x hx D hD T hT
  intro hxpos
  rcases hEitherClock hxpos with ⟨n, hnT, hbound⟩ | ⟨η, hη, hbound⟩
  · refine ⟨fun _ => (n : ℝ≥0∞), ?_, ?_⟩
    · apply Filter.Eventually.of_forall
      intro ω
      have hlt : ENNReal.ofReal T < ENNReal.ofReal (n : ℝ) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hT).2 hnT
      simpa only [ENNReal.ofReal_natCast] using hlt
    · simpa only [] using hbound
  · exact ⟨η, hη, hbound⟩
