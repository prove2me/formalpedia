-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T19:39:47.897166+00:00
-- url     : https://prove2.me/submissions/18ef125b-54fd-4559-afce-2dbe3e1442c0

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_indepStoppingWeight_futureReward_lintegral_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Random-clock survival and an independent future-path event factorise. -/
theorem solution
    {Ω Θ β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Θ] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (Y : Ω → β) (hY : Measurable Y)
    (hInd : IndepFun τ Y P)
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} =
      (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} * P (Y ⁻¹' B) := by
  let reward : β → ℝ≥0∞ := B.indicator (fun _ => 1)
  have hr : Measurable reward := measurable_const.indicator hB
  have hs : MeasurableSet {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} :=
    (measurableSet_lt (hτ.comp measurable_fst)
      (he.comp measurable_snd)).inter ((hY.comp measurable_fst) hB)
  have hs0 : MeasurableSet {z : Ω × Θ | τ z.1 < e z.2} :=
    measurableSet_lt (hτ.comp measurable_fst) (he.comp measurable_snd)
  have hsection (ω : Ω) :
      Q (Prod.mk ω ⁻¹'
        {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B}) =
      discount (τ ω) * reward (Y ω) := by
    by_cases hω : Y ω ∈ B
    · have heq : (Prod.mk ω ⁻¹'
          {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B}) =
          {η : Θ | τ ω < e η} := by
        ext η
        simp [hω]
      rw [heq, hTail (τ ω)]
      simp [reward, hω]
    · have heq : (Prod.mk ω ⁻¹' {z : Ω × Θ |
          τ z.1 < e z.2 ∧ Y z.1 ∈ B}) = ∅ := by
        ext η
        simp [hω]
      rw [heq]
      simp [reward, hω]
  have hfirst :
      (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} =
        ∫⁻ ω, discount (τ ω) * reward (Y ω) ∂P := by
    rw [Measure.prod_apply hs]
    congr 1
    funext ω
    exact hsection ω
  have hbase :
      (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} =
        ∫⁻ ω, discount (τ ω) ∂P := by
    rw [Measure.prod_apply hs0]
    congr 1
    funext ω
    change Q {η : Θ | τ ω < e η} = discount (τ ω)
    exact hTail (τ ω)
  have hreward : (∫⁻ ω, reward (Y ω) ∂P) = P (Y ⁻¹' B) := by
    have heq : (fun ω : Ω => reward (Y ω)) =
        (Y ⁻¹' B).indicator (fun _ : Ω => (1 : ℝ≥0∞)) := by
      funext ω
      by_cases hω : Y ω ∈ B <;> simp [reward, hω]
    rw [heq]
    exact lintegral_indicator_fun_one (hY hB)
  calc
    (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2 ∧ Y z.1 ∈ B} =
        ∫⁻ ω, discount (τ ω) * reward (Y ω) ∂P := hfirst
    _ = (∫⁻ ω, discount (τ ω) ∂P) *
        (∫⁻ ω, reward (Y ω) ∂P) :=
      AvramDividend.Classical.indepStoppingWeight_futureReward_lintegral_factor
        P τ hτ Y hY hInd discount hd reward hr
    _ = (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} * P (Y ⁻¹' B) := by
      rw [hbase, hreward]
