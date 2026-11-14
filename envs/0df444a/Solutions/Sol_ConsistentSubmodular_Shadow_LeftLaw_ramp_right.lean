-- Prove2me | solution 1 for ConsistentSubmodular.Shadow.LeftLaw.ramp_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:02.490082+00:00
-- url     : https://prove2.me/submissions/dec5f2f8-75f2-492d-9e8a-655a66032684

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

section

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem solution (x : ℝ) : ∀ᶠ h in 𝓝[≥] (0 : ℝ), L.ramp (x + h) = L.ramp x + L.cdf x * h := by
  have key : ∀ j, ∀ᶠ h in 𝓝[≥] (0 : ℝ), max 0 (x + h - L.left j) =
      max 0 (x - L.left j) + (if L.left j ≤ x then h else 0) := by
    intro j
    by_cases hj : L.left j ≤ x
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 ≤ h)
      rw [if_pos hj, max_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [not_le] at hj
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (sub_pos.mpr hj))] with h
        (hh : h < L.left j - x)
      rw [if_neg (not_le.mpr hj), max_eq_left (by linarith), max_eq_left (by linarith)]
      ring
  filter_upwards [Filter.eventually_all.2 key] with h hh
  simp only [ramp, cdf, hh, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

end
