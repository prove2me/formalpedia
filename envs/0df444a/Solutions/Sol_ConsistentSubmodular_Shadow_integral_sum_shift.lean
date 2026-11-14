-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.integral_sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:37.609543+00:00
-- url     : https://prove2.me/submissions/09d589eb-5581-42d4-89b9-c7c92507b34e

import Mathlib

section

noncomputable section

open scoped BigOperators Topology

open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

/-- A bounded measurable function is integrable on every bounded interval. -/
theorem intervalIntegrable_of_bounded {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  constructor <;>
  exact Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hC x)

end ConsistentSubmodular.Shadow

end

end

section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow

theorem solution {φ : ℝ → ℝ} (hφ : Measurable φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (N : ℕ) : ∫ s in (0 : ℝ)..1, ∑ j ∈ Finset.range N, φ (s + j) = ∫ y in (0 : ℝ)..N, φ y := by
  rw [intervalIntegral.integral_finset_sum (s := Finset.range N)
    (f := fun (j : ℕ) (s : ℝ) => φ (s + j)) fun j _ =>
      intervalIntegrable_of_bounded (f := fun s : ℝ => φ (s + j))
        (hφ.comp (measurable_add_const _)) (fun x => hC _) 0 1]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ)
    (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ => intervalIntegrable_of_bounded hφ hC _ _
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_comp_add_right]
  push_cast
  ring_nf

end
