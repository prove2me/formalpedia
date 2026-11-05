-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_assist_p3_original_source_cap_C1_grid_premises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:46:54.193228+00:00
-- url     : https://prove2.me/submissions/498a118b-7085-4464-9324-6c23450c22b0

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_finite_cap_extension_idempotent
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_C1_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

/-- The exact source cap continuation satisfies the entire P3-F w := V premise bundle. -/
theorem solution
    (C : ℝ≥0∞) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z) :
    ContinuousOn V (Ici (0 : ℝ)) ∧
    ContDiffOn ℝ 1 V {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} ∧
    (∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv V z) ∧
    (C = ⊤ → ∀ z : ℝ, V z = V z) ∧
    (C ≠ ⊤ → ∀ z : ℝ, V z =
      if z ≤ C.toReal then V z
      else V C.toReal + (z - C.toReal)) := by
  refine ⟨
    avram_p2_assist_p3_cap_extension_continuousOn_nonnegative
      C w V hVtop hVfinite hw_cont,
    avram_p2_assist_p3_cap_extension_C1_strict_interior
      C w V hVtop hVfinite hw_smooth,
    ?_, ?_, ?_⟩
  · intro z hz0 hzC
    rw [avram_p2_assist_p3_cap_extension_deriv_eq_strict_interior
      C w V hVtop hVfinite z ⟨hz0, hzC⟩]
    exact hw_grad z hz0 hzC
  · intro hC z
    rfl
  · intro hC
    exact avram_p2_assist_p3_finite_cap_extension_idempotent
      C hC w V (hVfinite hC)
