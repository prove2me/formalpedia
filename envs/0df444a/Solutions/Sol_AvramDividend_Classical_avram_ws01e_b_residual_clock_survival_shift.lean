-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_residual_clock_survival_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T21:33:20.348313+00:00
-- url     : https://prove2.me/submissions/e9065dfb-c244-49b4-8e72-8abc3ec3159f

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_random_clock_tail_future_event_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- At a genuine independent memoryless observation clock, survival beyond
an independent random age plus a fixed increment separates both the elapsed
time increment and any future-path event. This uses the same stopped age for
the clock and the future path; it does not assume Wiener–Hopf splitting. -/
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
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0,
      discount (a + t) = factor t * discount a)
    (t : ℝ≥0) (B : Set β) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} =
      factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} *
        P (Y ⁻¹' B) := by
  have hτt : Measurable (fun ω : Ω => τ ω + t) :=
    hτ.add measurable_const
  have hshift : Measurable (fun a : ℝ≥0 => a + t) :=
    measurable_id.add measurable_const
  have hIndt : IndepFun (fun ω : Ω => τ ω + t) Y P := by
    simpa only [Function.comp_def, id_eq] using
      (hInd.comp hshift measurable_id)
  have hjoint :
      (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2 ∧ Y z.1 ∈ B} =
        (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2} *
          P (Y ⁻¹' B) :=
    AvramDividend.Classical.avram_ws01e_b_random_clock_tail_future_event_factor
      P Q (fun ω => τ ω + t) hτt Y hY hIndt e he
      discount hd hTail B hB
  have hs : MeasurableSet
      {z : Ω × Θ | τ z.1 + t < e z.2} :=
    measurableSet_lt (hτt.comp measurable_fst)
      (he.comp measurable_snd)
  have hs0 : MeasurableSet
      {z : Ω × Θ | τ z.1 < e z.2} :=
    measurableSet_lt (hτ.comp measurable_fst)
      (he.comp measurable_snd)
  have hbase :
      (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2} =
        factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} := by
    calc
      (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2} =
          ∫⁻ ω, Q {η : Θ | τ ω + t < e η} ∂P := by
        rw [Measure.prod_apply hs]
        rfl
      _ = ∫⁻ ω, discount (τ ω + t) ∂P := by
        congr 1
        funext ω
        exact hTail (τ ω + t)
      _ = ∫⁻ ω, factor t * discount (τ ω) ∂P := by
        congr 1
        funext ω
        exact hShift (τ ω) t
      _ = factor t * (∫⁻ ω, discount (τ ω) ∂P) :=
        lintegral_const_mul (factor t) (hd.comp hτ)
      _ = factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} := by
        congr 1
        rw [Measure.prod_apply hs0]
        congr 1
        funext ω
        exact (hTail (τ ω)).symm
  simpa only [hbase] using hjoint
