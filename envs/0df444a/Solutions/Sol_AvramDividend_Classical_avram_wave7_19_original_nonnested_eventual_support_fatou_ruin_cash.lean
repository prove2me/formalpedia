-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_nonnested_eventual_support_fatou_ruin_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:40:57.813874+00:00
-- url     : https://prove2.me/submissions/0ec38d9c-fcb3-48f1-8cb7-9f3e0c47df7b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Genuine source ruin cash passes through eventually covering nonnested cap supports by Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (interior : ℕ → Set ℝ)
    (hBoundaryMeas : MeasurableSet boundary)
    (hInteriorMeas : ∀ n, MeasurableSet (interior n))
    (hEventual : ∀ t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ∀ᶠ n : ℕ in Filter.atTop, t ∈ boundary ∪ interior n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    Filter.liminf (fun n : ℕ =>
      ∫⁻ t in boundary ∪ interior n,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      Filter.atTop := by
  classical
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let A : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T
  let U : ℕ → Set ℝ := fun n => boundary ∪ interior n
  have hA : MeasurableSet A :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iic
  have hU (n : ℕ) : MeasurableSet (U n) :=
    hBoundaryMeas.union (hInteriorMeas n)
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  have hG (n : ℕ) : Measurable ((U n).indicator f) :=
    hf.indicator (hU n)
  have hPoint (t : ℝ) :
      (A.indicator f) t ≤ Filter.liminf
        (fun n : ℕ => ((U n).indicator f) t) Filter.atTop := by
    by_cases ht : t ∈ A
    · rw [Set.indicator_of_mem ht]
      have hEventually :
          (fun n : ℕ => ((U n).indicator f) t) =ᶠ[Filter.atTop]
            (fun _ : ℕ => f t) := by
        filter_upwards [hEventual t ht] with n hn
        have hUn : t ∈ U n := hn
        simp [Set.indicator, hUn]
      have hLim :
          Filter.liminf (fun n : ℕ => ((U n).indicator f) t) Filter.atTop =
            f t := by
        calc
          Filter.liminf (fun n : ℕ => ((U n).indicator f) t) Filter.atTop =
              Filter.liminf (fun _ : ℕ => f t) Filter.atTop :=
            Filter.liminf_congr hEventually
          _ = f t := Filter.liminf_const (f t)
      rw [hLim]
    · rw [Set.indicator_of_notMem ht]
      exact bot_le
  change (∫⁻ t in A, f t ∂μ) ≤
    Filter.liminf (fun n : ℕ => ∫⁻ t in U n, f t ∂μ) Filter.atTop
  calc
    (∫⁻ t in A, f t ∂μ) =
        ∫⁻ t, (A.indicator f) t ∂μ :=
      (lintegral_indicator hA f).symm
    _ ≤ ∫⁻ t, Filter.liminf
        (fun n : ℕ => ((U n).indicator f) t) Filter.atTop ∂μ :=
      lintegral_mono hPoint
    _ ≤ Filter.liminf
        (fun n : ℕ => ∫⁻ t, ((U n).indicator f) t ∂μ) Filter.atTop :=
      lintegral_liminf_le hG
    _ = Filter.liminf
        (fun n : ℕ => ∫⁻ t in U n, f t ∂μ) Filter.atTop := by
      congr 1
      funext n
      exact lintegral_indicator (hU n) f
