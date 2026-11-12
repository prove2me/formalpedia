-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb99_finite_step_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:19:21.439205+00:00
-- url     : https://prove2.me/submissions/5292db8c-dc52-45bd-904f-599e1bf86fa7

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (s : Finset ℕ) (a b : ℕ → ℝ) (g : ℕ → Ω → ℝ)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hb : ∀ i ∈ s, ∀ ω, |g i ω| ≤ B) (t : ℝ) (ω : Ω) :
    |s.sum (fun i => if a i ≤ t ∧ t < b i then g i ω else 0)| ≤
      (s.card : ℝ) * B := by
  classical
  calc
    _ ≤ s.sum (fun i => |if a i ≤ t ∧ t < b i then g i ω else 0|) :=
      Finset.abs_sum_le_sum_abs
        (fun i => if a i ≤ t ∧ t < b i then g i ω else 0) s
    _ ≤ s.sum (fun _ => B) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : a i ≤ t ∧ t < b i
      · simpa [h] using hb i hi ω
      · simp [h, hB0]
    _ = (s.card : ℝ) * B := by simp [mul_comm]
