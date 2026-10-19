-- Prove2me | solution 1 for CohnElkies.poissonLogistic_cosine_transform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/824f152c-c332-472a-8395-4fc42af8561b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_characteristic
import Theorems.Thm_CohnElkies_poissonLogistic_characteristic_integrable

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
    (∫ u : ℝ,
      poissonLogisticDensity u * Real.cos (t * u)) =
      if t = 0 then 1 else t / Real.sinh t := by
  calc
    (∫ u : ℝ,
      poissonLogisticDensity u * Real.cos (t * u)) =
        ∫ u : ℝ,
          ((poissonLogisticDensity u : ℂ) *
            Complex.exp
              (Complex.I * (t : ℂ) * (u : ℂ))).re := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hphase :
          Complex.I * (t : ℂ) * (u : ℂ) =
            ((t * u : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hphase, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.exp_ofReal_mul_I_re]
      ring
    _ =
      (∫ u : ℝ,
        (poissonLogisticDensity u : ℂ) *
          Complex.exp
            (Complex.I * (t : ℂ) * (u : ℂ))).re :=
      integral_re (poissonLogistic_characteristic_integrable t)
    _ = if t = 0 then 1 else t / Real.sinh t := by
      rw [poissonLogistic_characteristic t]
      split
      · simp
      · exact Complex.ofReal_re (t / Real.sinh t)
end CohnElkies
