-- Prove2me | solution 1 for FamousTheorems.descent_theorem_fg_groups
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:33:00.094889+00:00
-- url     : https://prove2.me/submissions/97acc433-e0a5-46fa-bb6c-1fcf80952572

import Mathlib

theorem solution {G : Type*} [CommGroup G] {h : G → ℝ} {C : ℝ} (hfi : (powMonoidHom 2 : G →* G).range.FiniteIndex)
    (hnn : ∀ x, 0 ≤ h x) (hpar : ∀ x y, |h (x * y) + h (x / y) - 2 * (h x + h y)| ≤ C)
    [Northcott h] : Group.FG G :=
  CommGroup.fg_of_descent' hfi hnn hpar
