-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_stopped_physmesh_occupation_exact_full_interval
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:23:30.336585+00:00
-- url     : https://prove2.me/submissions/c109710a-7046-464d-a80a-6f8fcdb8cd04

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (b : ℝ) (T : ℝ≥0) (n : ℕ)
    (hT : 0 < T) (hTn : (T : ℝ) ≤ (n : ℝ))
    (hFloor : ∀ t : ℝ, 0 < t → t < (T : ℝ) →
      b < f (Real.toNNReal t)) :
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if t < (T : ℝ) ∧ b < f (Real.toNNReal t)
        then (1 : ℝ) else 0) ∂volume) = (T : ℝ) := by
  have hEq : EqOn
      (fun t : ℝ => if t < (T : ℝ) ∧ b < f (Real.toNNReal t)
        then (1 : ℝ) else 0)
      ((Ioo (0 : ℝ) (T : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)))
      (Ioo (0 : ℝ) (n : ℝ)) := by
    intro t ht
    by_cases htt : t < (T : ℝ)
    · have hf := hFloor t ht.1 htt
      simp [Set.indicator, Set.mem_Ioo, ht.1, htt, hf]
    · simp [Set.indicator, Set.mem_Ioo, htt]
  have hInt : Ioo (0 : ℝ) (n : ℝ) ∩ Ioo (0 : ℝ) (T : ℝ) =
      Ioo (0 : ℝ) (T : ℝ) := by
    ext t
    constructor
    · exact fun ht => ht.2
    · intro ht
      exact ⟨⟨ht.1, lt_of_lt_of_le ht.2 hTn⟩, ht⟩
  calc
    (∫ t in Ioo (0 : ℝ) (n : ℝ),
      (if t < (T : ℝ) ∧ b < f (Real.toNNReal t)
        then (1 : ℝ) else 0) ∂volume) =
      (∫ t in Ioo (0 : ℝ) (n : ℝ),
        (Ioo (0 : ℝ) (T : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) t
        ∂volume) := setIntegral_congr_fun measurableSet_Ioo hEq
    _ = ∫ t in Ioo (0 : ℝ) (T : ℝ), (1 : ℝ) ∂volume := by
      rw [setIntegral_indicator measurableSet_Ioo, hInt]
    _ = (T : ℝ) := by
      rw [setIntegral_const, smul_eq_mul, mul_one]
      simp [Measure.real, Real.volume_Ioo, (show 0 ≤ (T : ℝ) from hT.le)]
