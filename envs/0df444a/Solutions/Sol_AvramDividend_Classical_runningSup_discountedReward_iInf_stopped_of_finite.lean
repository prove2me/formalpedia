-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_discountedReward_iInf_stopped_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:22:15.124885+00:00
-- url     : https://prove2.me/submissions/87cb4421-b031-4f8c-be17-52afcb0bbfb9

import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_restrict_eq
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Integrable discounted regulator rewards are continuous at decreasing ruin horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Antitone σ)
    (q : ℝ)
    (hfinite : ∫⁻ t in paymentTimes (σ 0),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω) ≠ ⊤) :
    (∫⁻ t in paymentTimes (⨅ n, σ n),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) =
    ⨅ n, (∫⁻ t in paymentTimes (σ n),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure (runningSup X) ω)) := by
  let μ := dividendMeasure (runningSup X) ω
  let w : ℝ → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let f : ℕ → ℝ → ℝ≥0∞ :=
    fun n => (paymentTimes (σ n)).indicator w
  have hw : Measurable w := by
    dsimp [w]
    fun_prop
  have hmeas (n : ℕ) : Measurable (f n) :=
    hw.indicator (paymentTimes_measurable (σ n))
  have hanti : Antitone f := by
    intro i j hij t
    have hsub : paymentTimes (σ j) ⊆ paymentTimes (σ i) := by
      intro s hs
      exact ⟨hs.1, hs.2.imp id
        (fun h => lt_of_lt_of_le h (hσ hij))⟩
    by_cases ht : t ∈ paymentTimes (σ j)
    · have hit := hsub ht
      simp only [f, Set.indicator_of_mem ht,
        Set.indicator_of_mem hit, le_refl]
    · simp [f, Set.indicator, ht]
  have hfinite' : ∫⁻ t, f 0 t ∂μ ≠ ⊤ := by
    simpa only [f, lintegral_indicator
      (paymentTimes_measurable (σ 0))] using hfinite
  have hlim (t : ℝ) :
      (⨅ n, f n t) =
        (⋂ n, paymentTimes (σ n)).indicator w t := by
    by_cases ht : ∀ n, t ∈ paymentTimes (σ n)
    · have hmem : t ∈ ⋂ n, paymentTimes (σ n) :=
        Set.mem_iInter.mpr ht
      simp only [Set.indicator_of_mem hmem]
      simp only [f, Set.indicator_of_mem (ht _), iInf_const]
    · push_neg at ht
      obtain ⟨n, hn⟩ := ht
      have hnot : t ∉ ⋂ n, paymentTimes (σ n) := by
        intro h
        exact hn (Set.mem_iInter.mp h n)
      have hzero : (⨅ k, f k t) = 0 := by
        apply bot_unique
        calc
          (⨅ k, f k t) ≤ f n t := iInf_le _ n
          _ = 0 := by simp [f, Set.indicator, hn]
      simpa [Set.indicator, hnot] using hzero
  have hMCT := lintegral_iInf hmeas hanti hfinite'
  have heq := runningSup_paymentTimes_iInter_restrict_eq X ω σ
  have hwindow : (∫⁻ t in paymentTimes (⨅ n, σ n), w t ∂μ) =
      ∫⁻ t in (⋂ n, paymentTimes (σ n)), w t ∂μ := by
    exact congrArg (fun ν : Measure ℝ => ∫⁻ t, w t ∂ν) heq.symm
  calc
    (∫⁻ t in paymentTimes (⨅ n, σ n), w t ∂μ) =
        ∫⁻ t, ⨅ n, f n t ∂μ := by
      rw [hwindow, ← lintegral_indicator
        (MeasurableSet.iInter (fun n => paymentTimes_measurable (σ n)))]
      simp_rw [hlim]
    _ = ⨅ n, (∫⁻ t, f n t ∂μ) := hMCT
    _ = ⨅ n, (∫⁻ t in paymentTimes (σ n), w t ∂μ) := by
      simp_rw [f, lintegral_indicator (paymentTimes_measurable _)]
