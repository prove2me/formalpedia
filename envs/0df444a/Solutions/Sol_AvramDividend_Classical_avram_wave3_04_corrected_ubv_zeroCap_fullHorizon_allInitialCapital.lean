-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:07:23.842724+00:00
-- url     : https://prove2.me/submissions/824fd343-19cc-44c2-ac76-959a0ae03cbe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Complete zero-cap branch of the corrected unbounded-variation
finite-horizon stochastic verification, with full original Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ (0 : ℝ≥0∞))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x 0 D)
    (q : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hx0 := avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
    X x hxc D hD
  subst x
  have hzero := avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero
    X hBV D hD q T.toNNReal
  have hco : ((T.toNNReal : ℝ≥0) : ℝ) = T :=
    Real.coe_toNNReal T hT
  simp only [hco] at hzero
  rw [hzero]
  exact bot_le
