-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite53_original_interior_C2_derivative_certificates
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:34:34.046886+00:00
-- url     : https://prove2.me/submissions/0a0ab783-118f-4bcd-9149-95897b9f67c1

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped ENNReal Topology
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (y : ℝ) (hy0 : 0 < y) (hyC : ENNReal.ofReal y < C) :
    HasDerivAt w (deriv w y) y ∧
      HasDerivAt (deriv w) (iteratedDeriv 2 w y) y := by
  have hOpen : IsOpen {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by
    change IsOpen ({z : ℝ | 0 < z} ∩
      {z : ℝ | ENNReal.ofReal z < C})
    exact (isOpen_lt continuous_const continuous_id).inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hAt : ContDiffAt ℝ 2 w y :=
    hw_smooth.contDiffAt (hOpen.mem_nhds ⟨hy0, hyC⟩)
  have hAtDer : ContDiffAt ℝ 1 (deriv w) y :=
    hAt.derivWithin (by norm_num)
  constructor
  · exact (hAt.differentiableAt (by norm_num)).hasDerivAt
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hAtDer.differentiableAt (by norm_num)).hasDerivAt
