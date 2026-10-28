-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_discountedDividend_zero_if_ruin_before_upcrossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:45:56.50614+00:00
-- url     : https://prove2.me/submissions/6f010dda-e638-458b-a651-47239170893b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_dividendMeasure_zero_through_firstUpcrossing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- If the controlled reserve is ruined before reaching the barrier, no
    discounted Stieltjes dividend payments occur. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x a : ℝ)
    (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : a - x < X.X s ω), (s : ℝ≥0∞)))
    (hruin : ruinTime X x (barrierStrategy X x a) ω ≤ (u : ℝ≥0∞)) :
    (∫⁻ t in paymentTimes (ruinTime X x (barrierStrategy X x a) ω),
       ENNReal.ofReal (Real.exp (-(q * t)))
       ∂(dividendMeasure (barrierStrategy X x a) ω)) = 0 := by
  let D := barrierStrategy X x a
  let τ := ruinTime X x D ω
  let μ := dividendMeasure D ω
  have hsub : paymentTimes τ ⊆ Set.Icc (0 : ℝ) (u : ℝ) := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    rcases ht.2 with hzero | hlt
    · subst t
      exact ⟨le_refl _, u.property⟩
    · have hle : ENNReal.ofReal t ≤ (u : ℝ≥0∞) :=
        le_trans (le_of_lt hlt) hruin
      have hreal : t ≤ (u : ℝ) := by
        have ht_coe := ENNReal.toReal_le_coe_of_le_coe hle
        simpa [ENNReal.toReal_ofReal ht0] using ht_coe
      exact ⟨ht0, hreal⟩
  have hwindow : μ (Set.Icc (0 : ℝ) (u : ℝ)) = 0 :=
    barrierStrategy_dividendMeasure_zero_through_firstUpcrossing
      X x a hx0 hxa ω u hu
  have hbound : μ (paymentTimes τ) ≤ 0 := by
    calc
      μ (paymentTimes τ) ≤ μ (Set.Icc (0 : ℝ) (u : ℝ)) := measure_mono hsub
      _ = 0 := hwindow
  have hzero : μ (paymentTimes τ) = 0 :=
    le_antisymm hbound (by exact zero_le)
  exact setLIntegral_measure_zero _ _ hzero