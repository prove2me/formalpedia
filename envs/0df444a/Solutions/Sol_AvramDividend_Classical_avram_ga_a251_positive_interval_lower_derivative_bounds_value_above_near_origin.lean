-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a251_positive_interval_lower_derivative_bounds_value_above_near_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:44:17.011581+00:00
-- url     : https://prove2.me/submissions/d997c135-3f35-471a-93a2-f7f7200ab84e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (h : ℝ → ℝ) (a y M : ℝ)
    (hya : y ≤ a)
    (hCont : ContinuousOn h (Set.Icc y a))
    (hDiff : DifferentiableOn ℝ h (interior (Set.Icc y a)))
    (hLower : ∀ t ∈ interior (Set.Icc y a),
      -M ≤ deriv h t) :
    h y ≤ h a + M*(a-y) := by
  have hmv := (convex_Icc y a).mul_sub_le_image_sub_of_le_deriv
    hCont hDiff hLower
    y ⟨le_rfl,hya⟩ a ⟨hya,le_rfl⟩ hya
  linarith
