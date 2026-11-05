-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_physical_grid_real_rate_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:08:24.09207+00:00
-- url     : https://prove2.me/submissions/855f0173-953d-4547-85fe-5bd6c33ca9f2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
theorem solution
    (T a : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∑ i : Fin k, ((s i : ℝ) * (a : ℝ)) *
      (((t i - s i : ℝ≥0) : ℝ) * (a : ℝ))) =
      ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := by
  intro s t
  obtain ⟨hst, _, hs, ht⟩ :=
    avram_leanlevy_bridge_uniform_source_grid_endpoints T k hk
  calc
    (∑ i : Fin k, ((s i : ℝ) * (a : ℝ)) *
        (((t i - s i : ℝ≥0) : ℝ) * (a : ℝ))) =
      ∑ i : Fin k, (((i.val : ℝ) * (T : ℝ) / (k : ℝ)) *
        (a : ℝ)) * (((((i.val + 1 : ℕ) : ℝ) * (T : ℝ) /
        (k : ℝ)) - ((i.val : ℝ) * (T : ℝ) /
        (k : ℝ))) * (a : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [NNReal.coe_sub (hst i), hs i, ht i]
    _ = ((k : ℝ) * ((k : ℝ) - 1) / 2) *
        (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2) := by
          let f : ℕ → ℝ := fun i =>
            (((i : ℝ) * (T : ℝ)) / (k : ℝ) * (a : ℝ)) *
              (((((i + 1 : ℕ) : ℝ) * (T : ℝ)) / (k : ℝ) -
                ((i : ℝ) * (T : ℝ)) / (k : ℝ)) * (a : ℝ))
          change (∑ i : Fin k, f i.val) =
            ((k : ℝ) * ((k : ℝ) - 1) / 2) *
              (((T : ℝ) * (a : ℝ)) ^ 2 / (k : ℝ) ^ 2)
          rw [Fin.sum_univ_eq_sum_range]
          simpa only [f, Nat.cast_add, Nat.cast_one] using
            (avram_leanlevy_bridge_original_equal_mesh_triangular_rate_real
              (T : ℝ) (a : ℝ) k)
