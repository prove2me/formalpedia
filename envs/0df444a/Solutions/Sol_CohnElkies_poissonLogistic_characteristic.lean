-- Prove2me | solution 1 for CohnElkies.poissonLogistic_characteristic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/e49a33dc-b64e-4176-a014-bf7550ff5c3b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_poissonLogisticDensity
import Theorems.Thm_CohnElkies_poissonLogistic_characteristic_of_ne_zero

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
      (poissonLogisticDensity u : ℂ) *
        Complex.exp
          (Complex.I * (t : ℂ) * (u : ℂ))) =
      if t = 0 then 1 else
        ((t / Real.sinh t : ℝ) : ℂ) := by
  by_cases ht : t = 0
  · subst t
    simp only [Complex.ofReal_zero, mul_zero, zero_mul,
      Complex.exp_zero, mul_one, ↓reduceIte]
    let m : ℝ := ∫ u : ℝ, poissonLogisticDensity u
    have hm : m = 1 := integral_poissonLogisticDensity
    calc
      (∫ u : ℝ, (poissonLogisticDensity u : ℂ)) =
          (m : ℂ) := by
        try dsimp [m]
        exact integral_ofReal
      _ = 1 := by
        rw [hm]
        norm_num
  · simpa [ht] using!
      poissonLogistic_characteristic_of_ne_zero ht
end CohnElkies
