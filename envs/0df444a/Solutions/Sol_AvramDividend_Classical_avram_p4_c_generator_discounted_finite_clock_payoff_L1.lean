-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_finite_clock_payoff_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:38:20.804952+00:00
-- url     : https://prove2.me/submissions/698c0b11-1af6-4c2f-a2ed-19e09bf6a91f

import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- The discounted -q*w term of the original stopped HJB residual is L¹
on a finite interior clock whenever the sampled payoff is bounded there. -/
theorem solution
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) [IsFiniteMeasure μ]
    (R : T → ℝ) (clock : T → ℝ≥0) (w : ℝ → ℝ) (q : ℝ)
    (hwmeas : Measurable (fun t => w (R t)))
    (hclock : Measurable clock)
    (hq : 0 ≤ q) (A : Set T) (hA : MeasurableSet A)
    (B : ℝ) (hbound : ∀ t ∈ A, |w (R t)| ≤ B) :
    Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) * w (R t))) μ := by
  classical
  let v : T → ℝ := fun t => w (R t)
  have hvint : Integrable (A.indicator v) μ := by
    apply (integrable_const |B|).mono'
      (hwmeas.indicator hA).aestronglyMeasurable
    filter_upwards [] with t
    by_cases ht : t ∈ A
    · simpa only [Set.indicator_of_mem ht, Real.norm_eq_abs, v] using
        (hbound t ht).trans (le_abs_self B)
    · simp [Set.indicator, ht]
  let a : T → ℝ := fun t => Real.exp (-(q * (clock t : ℝ)))
  have hameas : Measurable a := by
    dsimp [a]
    fun_prop
  have habound : ∀ t, |a t| ≤ (1 : ℝ) := by
    intro t
    change |Real.exp (-(q * (clock t : ℝ)))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    have ht : 0 ≤ (clock t : ℝ) := (clock t).property
    have hle : -(q * (clock t : ℝ)) ≤ 0 :=
      neg_nonpos.mpr (mul_nonneg hq ht)
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr hle)
  have hweighted : Integrable (fun t => a t * A.indicator v t) μ := by
    apply Integrable.bdd_mul hvint hameas.aestronglyMeasurable (c := 1)
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using habound t
  have hEq : A.indicator (fun t => a t * v t) =
      (fun t => a t * A.indicator v t) := by
    funext t
    by_cases ht : t ∈ A
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  change Integrable (A.indicator (fun t => a t * v t)) μ
  rw [hEq]
  exact hweighted
