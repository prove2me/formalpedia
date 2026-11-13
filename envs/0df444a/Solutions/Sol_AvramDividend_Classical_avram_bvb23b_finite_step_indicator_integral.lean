-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23b_finite_step_indicator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:18:08.873858+00:00
-- url     : https://prove2.me/submissions/13d4c3bc-3ec0-45c9-9cfd-e10dc7a68676

import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped BigOperators
noncomputable section

theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (s : ℕ → Set α) (hs : ∀ i, MeasurableSet (s i))
    (w : ℕ → ℝ) (n : ℕ) :
    (∫ x, ∑ i ∈ Finset.range n, (s i).indicator (fun _ => w i) x ∂μ) =
      ∑ i ∈ Finset.range n, w i * (μ (s i)).toReal := by
  rw [integral_finset_sum (Finset.range n) (by
    intro i hi
    exact (integrable_const (w i)).indicator (hs i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_indicator (hs i)]
  simp [integral_const, Measure.real_def, smul_eq_mul, mul_comm]
