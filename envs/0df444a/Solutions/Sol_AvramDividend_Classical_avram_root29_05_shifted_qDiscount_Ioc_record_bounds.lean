-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_qDiscount_Ioc_record_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:37:52.112054+00:00
-- url     : https://prove2.me/submissions/2b4b0589-235d-41da-adf1-0216edaf3848

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shiftedSup_stieltjes_Ioc_eq_record_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Endpoint discount bounds for the genuine Stieltjes cash measure
of any finite-age shifted Lévy future running supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (age : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (ENNReal.ofReal (Real.exp (-(q * t))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
      ∫⁻ r, if r ∈ Ioc s t then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ∧
    ((∫⁻ r, if r ∈ Ioc s t then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal (M t.toNNReal - M s.toNNReal)) := by
  let M : ℝ≥0 → ℝ := fun v =>
    sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
  let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
  let w : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-(q * r)))
  have hAnti : Antitone w := by
    intro x y hxy
    have hMul : q * x ≤ q * y := mul_le_mul_of_nonneg_left hxy hq
    exact ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp_of_le (neg_le_neg hMul))
  have hMass : μ (Ioc s t) =
      ENNReal.ofReal (M t.toNNReal - M s.toNNReal) := by
    simpa only [μ, M] using
      (avram_root29_05_shiftedSup_stieltjes_Ioc_eq_record_increment
        X ω age s t)
  have hConst (c : ℝ≥0∞) :
      (∫⁻ r, if r ∈ Ioc s t then c else 0 ∂μ) =
        c * μ (Ioc s t) := by
    simpa only [Set.indicator] using
      (lintegral_indicator_const (μ := μ)
        (s := Ioc s t) measurableSet_Ioc c)
  have hLo :
      (∫⁻ r, if r ∈ Ioc s t then w t else 0 ∂μ) ≤
      (∫⁻ r, if r ∈ Ioc s t then w r else 0 ∂μ) := by
    apply lintegral_mono
    intro r
    by_cases hr : r ∈ Ioc s t
    · simpa only [if_pos hr] using hAnti hr.2
    · simp [hr]
  have hHi :
      (∫⁻ r, if r ∈ Ioc s t then w r else 0 ∂μ) ≤
      (∫⁻ r, if r ∈ Ioc s t then w s else 0 ∂μ) := by
    apply lintegral_mono
    intro r
    by_cases hr : r ∈ Ioc s t
    · simpa only [if_pos hr] using hAnti hr.1.le
    · simp [hr]
  change (w t * ENNReal.ofReal (M t.toNNReal - M s.toNNReal) ≤
    ∫⁻ r, if r ∈ Ioc s t then w r else 0 ∂μ) ∧
    ((∫⁻ r, if r ∈ Ioc s t then w r else 0 ∂μ) ≤
      w s * ENNReal.ofReal (M t.toNNReal - M s.toNNReal))
  constructor
  · calc
      _ = (∫⁻ r, if r ∈ Ioc s t then w t else 0 ∂μ) := by
            rw [hConst, hMass]
      _ ≤ _ := hLo
  · calc
      _ ≤ (∫⁻ r, if r ∈ Ioc s t then w s else 0 ∂μ) := hHi
      _ = _ := by rw [hConst, hMass]
