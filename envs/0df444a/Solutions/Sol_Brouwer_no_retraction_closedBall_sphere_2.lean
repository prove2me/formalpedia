-- Prove2me | solution 2 for Brouwer.no_retraction_closedBall_sphere
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T04:54:06.635288+00:00
-- url     : https://prove2.me/submissions/fa2ef095-9dcf-4b4a-ab9b-09e6b5379220

import Mathlib
import Theorems.Thm_OAI_PettyProjection_FixedPoint_no_C1_retraction_closedBall

open Metric Set MeasureTheory

-- The platform already has this impossibility in a stronger form: it asks only for a
-- derivative on the closed ball itself, continuous there, and never mentions an ambient open
-- set or the dimension. A `ContDiffOn ℝ 1` retraction on an open neighbourhood of the ball
-- supplies both, so this statement follows; `hd : 0 < d` turns out not to be needed, since the
-- hypotheses are already contradictory when `d = 0`.
theorem solution {d : ℕ} (hd : 0 < d)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hBU : closedBall 0 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x) : False := by
  have hdiff : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      HasFDerivWithinAt r (fderiv ℝ r x) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) x := by
    intro x hx
    have hxU : x ∈ U := hBU hx
    have : DifferentiableAt ℝ r x :=
      ((hr.differentiableOn one_ne_zero) x hxU).differentiableAt (hU.mem_nhds hxU)
    exact this.hasFDerivAt.hasFDerivWithinAt
  refine OAI.PettyProjection.FixedPoint.no_C1_retraction_closedBall
    (r := r) (r' := fun x => fderiv ℝ r x) hdiff ?_ ?_ ?_
  · exact (hr.continuousOn_fderiv_of_isOpen hU le_rfl).mono hBU
  · intro x hx
    exact mem_sphere_zero_iff_norm.mp (hmaps hx)
  · intro x hx
    exact hid x (mem_sphere_zero_iff_norm.mpr hx)
