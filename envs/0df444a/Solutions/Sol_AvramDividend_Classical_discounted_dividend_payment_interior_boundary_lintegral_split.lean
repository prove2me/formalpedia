-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividend_payment_interior_boundary_lintegral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:43:08.015249+00:00
-- url     : https://prove2.me/submissions/a186eafb-1f70-45ab-9a3b-f5cce5f66b54

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every nonnegative stopped dividend Stieltjes payout splits exactly into its contribution at strictly positive below-cap reserve times and the remaining zero-reserve or cap-boundary times. The interior and boundary parts form a disjoint measurable partition of the genuine payment window. This is a localisation interface for applying the HJB inequalities only where their hypotheses hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω)
    (C : ℝ≥0∞) (u : ℝ → ℝ)
    (hInterior : MeasurableSet {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C})
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ), f t ∂(dividendMeasure D ω)) =
      (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩ {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
        f t ∂(dividendMeasure D ω)) +
      (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \ {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
        f t ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  let I : Set ℝ := {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}
  have hBoundary : MeasurableSet (A \ I) :=
    ((paymentTimes_measurable σ).inter measurableSet_Iic).diff hInterior
  have hdisj : Disjoint (A ∩ I) (A \ I) := by
    refine Set.disjoint_left.mpr ?_
    intro t htA htB
    exact htB.2 htA.2
  have hsplit : A = (A ∩ I) ∪ (A \ I) := by
    ext t
    constructor
    · intro ht
      by_cases hi : t ∈ I
      · exact Or.inl ⟨ht, hi⟩
      · exact Or.inr ⟨ht, hi⟩
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩)
      · exact ht
      · exact ht
  change (∫⁻ t in A, f t ∂(dividendMeasure D ω)) =
    (∫⁻ t in A ∩ I, f t ∂(dividendMeasure D ω)) +
    (∫⁻ t in A \ I, f t ∂(dividendMeasure D ω))
  conv_lhs => rw [hsplit]
  exact lintegral_union hBoundary hdisj
