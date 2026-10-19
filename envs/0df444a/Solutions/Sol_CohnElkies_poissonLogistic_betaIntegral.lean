-- Prove2me | solution 1 for CohnElkies.poissonLogistic_betaIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/38e83705-95ad-431b-93ef-85b2a6d3c397

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_cpow_ratio
import Theorems.Thm_CohnElkies_integral_poissonLogistic_change_Ioo

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (w : ℂ) :
    Complex.betaIntegral (1 + w) (1 - w) =
      ∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
  calc
    Complex.betaIntegral (1 + w) (1 - w) =
        ∫ x : ℝ in Ioo 0 1,
          (x : ℂ) ^ w *
            (((1 - x : ℝ) : ℂ) ^ (-w)) := by
      unfold Complex.betaIntegral
      rw [intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 1 by norm_num),
        integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x _
      push_cast
      congr 1 <;> ring_nf
    _ = ∫ u : ℝ,
        poissonLogisticDensity u •
          (((poissonLogistic u : ℝ) : ℂ) ^ w *
            (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w))) :=
      integral_poissonLogistic_change_Ioo
        (fun x : ℝ =>
          (x : ℂ) ^ w * (((1 - x : ℝ) : ℂ) ^ (-w)))
    _ = ∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp (((Real.pi * u : ℝ) : ℂ) * w) := by
      apply integral_congr_ae
      filter_upwards [] with u
      change
        (poissonLogisticDensity u : ℂ) *
            (((poissonLogistic u : ℝ) : ℂ) ^ w *
              (((1 - poissonLogistic u : ℝ) : ℂ) ^ (-w))) =
          (poissonLogisticDensity u : ℂ) *
            Complex.exp (((Real.pi * u : ℝ) : ℂ) * w)
      rw [poissonLogistic_cpow_ratio]
end CohnElkies
