-- Prove2me | solution 1 for CohnElkies.poissonLogistic_characteristic_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/ef16d4b0-46d4-4ec9-9c96-4f1d14ebc3d8

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogisticDensity_integrable

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (t : ℝ) :
    Integrable
      (fun u : ℝ =>
        (poissonLogisticDensity u : ℂ) *
          Complex.exp
            (Complex.I * (t : ℂ) * (u : ℂ))) := by
  have hcontinuous :
      Continuous (fun u : ℝ =>
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) := by
    fun_prop
  apply poissonLogisticDensity_integrable.mono'
    (poissonLogisticDensity_integrable.ofReal.aestronglyMeasurable.mul
      hcontinuous.aestronglyMeasurable)
  filter_upwards [] with u
  have hdensity : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  change
    ‖(poissonLogisticDensity u : ℂ) *
      Complex.exp
        (Complex.I * (t : ℂ) * (u : ℂ))‖ ≤
      poissonLogisticDensity u
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hdensity]
  have hphase :
      Complex.I * (t : ℂ) * (u : ℂ) =
        Complex.I * ((t * u : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hphase, Complex.norm_exp_I_mul_ofReal]
  simp
end CohnElkies
