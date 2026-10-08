-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_payment_feasible_nonnegative_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:37:13.167367+00:00
-- url     : https://prove2.me/submissions/457fb862-0382-40ec-87cd-0f6827853230

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (hx : 0 ≤ x) (ha : 0 ≤ a) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω) →
        rightLimit (barrierStrategy X x a) t ω -
            barrierStrategy X x a t ω ≤
          riskProcess X x (barrierStrategy X x a) t ω := by
  intro ω t ht
  by_cases ht0 : t = 0
  · subst t
    rw [AvramDividend.Classical.barrierStrategy_right_increment_formula X x a ω 0]
    have hmax : max 0 (x - a) ≤ x :=
      max_le hx (sub_le_self x ha)
    simpa [riskProcess, barrierStrategy, X.X_zero] using hmax
  · have hbefore :
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω :=
      ht.resolve_left ht0
    rw [AvramDividend.Classical.barrierStrategy_right_increment_formula X x a ω t,
      if_neg ht0]
    have hreserve :
        0 ≤ riskProcess X x (barrierStrategy X x a) t ω := by
      by_contra hnegative
      have hneg :
          riskProcess X x (barrierStrategy X x a) t ω < 0 :=
        lt_of_not_ge hnegative
      have hruin :
          ruinTime X x (barrierStrategy X x a) ω ≤ (t : ℝ≥0∞) := by
        unfold ruinTime
        exact iInf_le_of_le t
          (iInf_le
            (fun (_ : riskProcess X x (barrierStrategy X x a) t ω < 0) =>
              (t : ℝ≥0∞))
            hneg)
      exact (not_le_of_gt hbefore) hruin
    simpa using hreserve
