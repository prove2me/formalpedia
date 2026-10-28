-- Prove2me | solution 1 for AvramDividend.Classical.finite_activity_mesh_probability_bound_forces_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T15:07:50.878051+00:00
-- url     : https://prove2.me/submissions/0aa0fdca-c1c1-4dc3-a3de-8cbbfa47ea9e

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_uniform_mesh_gap_tendsto_zero
import Mathlib.Topology.Order.Basic
open AvramDividend.Classical Filter MeasureTheory Set Topology
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Any nonnegative probability bounded eventually by the finite-activity
uniform-mesh Laplace gap must vanish. -/
theorem solution
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (T a c : ℝ) (hT : 0 ≤ T) (hc : 0 ≤ c)
    (hBound : ∀ᶠ N : ℕ in atTop,
      c ≤ Real.exp a *
        ((N : ℝ) *
          (Real.exp (-(T / (N : ℝ) *
            ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
            Real.exp (-(T / (N : ℝ) *
              (ν (Iio (0 : ℝ))).toReal))))) :
    c = 0 := by
  have hGap :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) *
            (Real.exp (-(T / (N : ℝ) *
              ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
              Real.exp (-(T / (N : ℝ) *
                (ν (Iio (0 : ℝ))).toReal))))
        atTop (𝓝 (0 : ℝ)) :=
    finite_negative_jump_uniform_mesh_gap_tendsto_zero ν hFinite T hT
  have hLimit :
      Tendsto
        (fun N : ℕ =>
          Real.exp a * ((N : ℝ) *
            (Real.exp (-(T / (N : ℝ) *
              ∫ y in Iio (0 : ℝ), (1 - Real.exp ((N : ℝ) * y)) ∂ν)) -
              Real.exp (-(T / (N : ℝ) *
                (ν (Iio (0 : ℝ))).toReal)))))
        atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hGap)
  exact le_antisymm (ge_of_tendsto hLimit hBound) hc
