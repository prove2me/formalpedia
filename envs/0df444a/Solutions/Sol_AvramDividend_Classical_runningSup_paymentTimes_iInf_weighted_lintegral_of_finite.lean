-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_paymentTimes_iInf_weighted_lintegral_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:14:18.87827+00:00
-- url     : https://prove2.me/submissions/00747d01-4beb-49eb-9a26-5c4bbdf9845f

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_mono_horizon
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Weighted Stieltjes reward continuity from above at strict payment windows. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ) (f : ℝ → ℝ≥0∞)
    (hfinite :
      (∫⁻ t in paymentTimes (σ 0), f t
        ∂(dividendMeasure (runningSup X) ω)) ≠ ⊤) :
    (∫⁻ t in paymentTimes (⨅ n, σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) =
    ⨅ n, (∫⁻ t in paymentTimes (σ n), f t
      ∂(dividendMeasure (runningSup X) ω)) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let ν : Measure ℝ := μ.withDensity f
  have hanti : Antitone (fun n : ℕ => paymentTimes (σ n)) := by
    intro i j hij
    simpa using paymentTimes_min_mono_horizon ⊤ (σ j) (σ i) (hσ hij)
  have hsets : ∀ n, NullMeasurableSet (paymentTimes (σ n)) ν := by
    intro n
    exact (paymentTimes_measurable (σ n)).nullMeasurableSet
  have hfiniteν : ν (paymentTimes (σ 0)) ≠ ⊤ := by
    change (μ.withDensity f) (paymentTimes (σ 0)) ≠ ⊤
    rw [withDensity_apply f (paymentTimes_measurable (σ 0))]
    exact hfinite
  have hmeasure :
      ν (⋂ n, paymentTimes (σ n)) =
        ⨅ n, ν (paymentTimes (σ n)) :=
    hanti.measure_iInter hsets ⟨0, hfiniteν⟩
  have hmeas_inter : MeasurableSet (⋂ n, paymentTimes (σ n)) :=
    MeasurableSet.iInter (fun n => paymentTimes_measurable (σ n))
  have hrestricted :
      (∫⁻ t in (⋂ n, paymentTimes (σ n)), f t ∂μ) =
        (∫⁻ t in paymentTimes (⨅ n, σ n), f t ∂μ) := by
    exact congrArg (fun m : Measure ℝ => ∫⁻ t, f t ∂m)
      (runningSup_paymentTimes_iInter_restrict_eq X ω σ)
  calc
    (∫⁻ t in paymentTimes (⨅ n, σ n), f t
        ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in (⋂ n, paymentTimes (σ n)), f t ∂μ) :=
      hrestricted.symm
    _ = ν (⋂ n, paymentTimes (σ n)) := by
      exact (withDensity_apply f hmeas_inter).symm
    _ = ⨅ n, ν (paymentTimes (σ n)) := hmeasure
    _ = ⨅ n, (∫⁻ t in paymentTimes (σ n), f t
        ∂(dividendMeasure (runningSup X) ω)) := by
      congr 1
      funext n
      exact withDensity_apply f (paymentTimes_measurable (σ n))
