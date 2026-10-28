-- Prove2me | solution 1 for AvramDividend.Classical.chat04_full_killed_renewal_of_positive_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:23:01.355402+00:00
-- url     : https://prove2.me/submissions/b8edbab9-c2de-4592-8867-e83ab81aa4de

import Theorems.Thm_AvramDividend_Classical_chat04_zero_reserve_killed_renewal_of_positive_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_renewal_zero_horizon_or_negative_reserve
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The entire killed q-scale expectation identity follows from its
    strictly positive-reserve case. Negative reserves and the origin
    are discharged by previously proved boundary theorems. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hpositive : ∀ (x : ℝ), 0 < x → ∀ t : ℝ≥0,
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
        ENNReal.ofReal (W x))
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
    ENNReal.ofReal (W x) := by
  by_cases hxneg : x < 0
  · exact chat04_history_killed_renewal_zero_horizon_or_negative_reserve
      X q W hW x t (Or.inr hxneg)
  by_cases hxzero : x = 0
  · subst x
    simpa only [zero_add] using
      chat04_zero_reserve_killed_renewal_of_positive_reserve
        X q hq W hW hnbv t (fun a ha => hpositive a ha t)
  have hxle : 0 ≤ x := le_of_not_gt hxneg
  have hxpos : 0 < x := lt_of_le_of_ne hxle (Ne.symm hxzero)
  exact hpositive x hxpos t
