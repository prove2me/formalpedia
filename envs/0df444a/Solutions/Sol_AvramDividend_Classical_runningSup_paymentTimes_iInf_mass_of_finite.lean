-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_paymentTimes_iInf_mass_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:18:10.430535+00:00
-- url     : https://prove2.me/submissions/3b940fd2-61a7-4582-87ff-8ca09edf2b4a

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The regulator's stopped Stieltjes mass is continuous at a decreasing ruin horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ)
    (hfinite : (dividendMeasure (runningSup X) ω)
        (paymentTimes (σ 0)) ≠ ⊤) :
    (dividendMeasure (runningSup X) ω)
        (paymentTimes (⨅ n, σ n)) =
      ⨅ n, (dividendMeasure (runningSup X) ω)
        (paymentTimes (σ n)) := by
  let μ := dividendMeasure (runningSup X) ω
  have hanti : Antitone (fun n : ℕ => paymentTimes (σ n)) := by
    intro i j hij t ht
    exact ⟨ht.1, ht.2.imp id
      (fun h => lt_of_lt_of_le h (hσ hij))⟩
  have hmeas (n : ℕ) :
      NullMeasurableSet (paymentTimes (σ n)) μ :=
    (paymentTimes_measurable (σ n)).nullMeasurableSet
  have hcont : μ (⋂ n, paymentTimes (σ n)) =
      ⨅ n, μ (paymentTimes (σ n)) :=
    hanti.measure_iInter hmeas ⟨0, hfinite⟩
  have heq : μ (⋂ n, paymentTimes (σ n)) =
      μ (paymentTimes (⨅ n, σ n)) := by
    have hr := runningSup_paymentTimes_iInter_restrict_eq X ω σ
    have hu := congrArg (fun ν : Measure ℝ => ν Set.univ) hr
    simpa [μ] using hu
  exact heq.symm.trans hcont
