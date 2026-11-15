-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a259_one_sided_global_HJB_endpoint_exponential_Gaussian_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:51:53.672043+00:00
-- url     : https://prove2.me/submissions/920c5d7e-e05d-4251-98eb-78c754c8b0ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (K theta b y r : ℝ)
    (hK : 0 ≤ K) (hθ : 0 ≤ theta)
    (hy : y ≤ b) (hEnd : 0 < y+r)
    (hw : ∀ t : ℝ, 0 < t → w t ≤ K*Real.exp (theta*t)) :
    w (y+r) ≤
      (K*Real.exp (theta*b))*Real.exp (theta*r) := by
  have hExp : Real.exp (theta*y) ≤ Real.exp (theta*b) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy hθ)
  have h1 := hw (y+r) hEnd
  have hEq : Real.exp (theta*(y+r)) =
      Real.exp (theta*y)*Real.exp (theta*r) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    w (y+r) ≤ K*Real.exp (theta*(y+r)) := h1
    _ = (K*Real.exp (theta*y))*Real.exp (theta*r) := by
      rw [hEq]
      ring
    _ ≤ (K*Real.exp (theta*b))*Real.exp (theta*r) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hExp hK) (Real.exp_nonneg _)
