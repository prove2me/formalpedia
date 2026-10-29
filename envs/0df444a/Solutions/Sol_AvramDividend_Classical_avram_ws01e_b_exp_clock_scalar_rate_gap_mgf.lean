-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_exp_clock_scalar_rate_gap_mgf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T20:45:32.141563+00:00
-- url     : https://prove2.me/submissions/f9287ed0-180a-4632-a406-cf0d03aeee42

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
theorem solution (p a : ℝ) (hp : 0 < p) (ha : a < p) :
    ENNReal.ofReal (p - a) *
      (∫⁻ t : ℝ, exponentialPDF p t *
        ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) =
      ENNReal.ofReal p := by
  have hpos : 0 < p - a := sub_pos.mpr ha
  have hpdfP : Measurable (exponentialPDF (p - a)) := (measurable_exponentialPDFReal (p - a)).ennreal_ofReal
  have hpdfR : Measurable (exponentialPDF p) := (measurable_exponentialPDFReal p).ennreal_ofReal
  have hRealT : Measurable (fun t : ℝ => (Real.toNNReal t : ℝ)) := measurable_coe_nnreal_real.comp measurable_real_toNNReal
  have hExpT : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))) := ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp (hRealT.mul measurable_const))
  have hWeight : Measurable (fun t : ℝ => exponentialPDF p t * ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a))) := hpdfR.mul hExpT
  letI : IsProbabilityMeasure (expMeasure (p - a)) :=
    isProbabilityMeasure_expMeasure hpos
  have hMass : (∫⁻ t : ℝ, exponentialPDF (p - a) t ∂volume) = 1 := by
    have h := (show (∫⁻ t : ℝ, (1 : ℝ≥0∞)
        ∂(expMeasure (p - a))) = 1 by simp)
    change (∫⁻ t : ℝ, (1 : ℝ≥0∞)
        ∂(volume.withDensity (exponentialPDF (p - a)))) = 1 at h
    rw [lintegral_withDensity_eq_lintegral_mul volume hpdfP measurable_const] at h
    simpa using h
  have hDensity (t : ℝ) : ENNReal.ofReal (p - a) * exponentialPDF p t * ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) = ENNReal.ofReal p * exponentialPDF (p - a) t := by
    by_cases ht : 0 ≤ t
    · rw [exponentialPDF_of_nonneg ht,
          exponentialPDF_of_nonneg ht,
          Real.coe_toNNReal t ht]
      have hp0 : 0 ≤ p := hp.le
      have hpos0 : 0 ≤ p - a := hpos.le
      have hprod : 0 ≤ (p - a) * (p * Real.exp (-(p * t))) :=
        mul_nonneg hpos0 (mul_nonneg hp0 (Real.exp_nonneg _))
      rw [← ENNReal.ofReal_mul hpos0,
          ← ENNReal.ofReal_mul hprod,
          ← ENNReal.ofReal_mul hp0]
      congr 1
      have he : Real.exp (-(p * t)) * Real.exp (a * t) = Real.exp (-((p - a) * t)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        (p - a) * (p * Real.exp (-(p * t))) * Real.exp (t * a) =
            (p - a) * p * (Real.exp (-(p * t)) * Real.exp (a * t)) := by
              rw [mul_comm t a]
              ring
        _ = (p - a) * p * Real.exp (-((p - a) * t)) := by rw [he]
        _ = p * ((p - a) * Real.exp (-((p - a) * t))) := by ring
    · have hn : t < 0 := lt_of_not_ge ht
      simp [exponentialPDF_of_neg hn]
  have hRate : ENNReal.ofReal (p - a) * (∫⁻ t : ℝ, exponentialPDF p t * ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)) ∂volume) = ENNReal.ofReal p := by
    calc
      _ = (∫⁻ t : ℝ, ENNReal.ofReal (p - a) *
          (exponentialPDF p t *
            ENNReal.ofReal (Real.exp ((Real.toNNReal t : ℝ) * a)))
          ∂volume) := by
            rw [lintegral_const_mul]
            exact hWeight
      _ = (∫⁻ t : ℝ, ENNReal.ofReal p *
          exponentialPDF (p - a) t ∂volume) := by
            apply lintegral_congr
            intro t
            simpa only [mul_assoc] using hDensity t
      _ = ENNReal.ofReal p *
          (∫⁻ t : ℝ, exponentialPDF (p - a) t ∂volume) := by
            rw [lintegral_const_mul]
            exact hpdfP
      _ = ENNReal.ofReal p := by rw [hMass, mul_one]
  exact hRate
