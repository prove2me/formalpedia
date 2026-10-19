-- Prove2me | solution 1 for CohnElkies.integral_poissonLogistic_change_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/c8a9f4e3-2022-4317-9060-185240d08bd1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_poissonLogistic_image_univ
import Theorems.Thm_CohnElkies_poissonLogistic_hasDerivAt
import Theorems.Thm_CohnElkies_poissonLogistic_injective

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ x : ℝ in Ioo 0 1, f x) =
      ∫ u : ℝ, poissonLogisticDensity u •
        f (poissonLogistic u) := by
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt poissonLogistic
          (poissonLogisticDensity x) Set.univ x := by
    intro x _
    exact (poissonLogistic_hasDerivAt x).hasDerivWithinAt
  have hpositive (u : ℝ) : 0 < poissonLogisticDensity u := by
    unfold poissonLogisticDensity
    positivity
  have hrange :
      Set.range poissonLogistic = Ioo (0 : ℝ) 1 := by
    simpa only [Set.image_univ] using! poissonLogistic_image_univ
  have h := integral_image_eq_integral_abs_deriv_smul
    (f := poissonLogistic) (f' := poissonLogisticDensity)
    MeasurableSet.univ hderiv
    poissonLogistic_injective.injOn f
  simpa [hrange,
    abs_of_pos (hpositive _)] using! h
end CohnElkies
