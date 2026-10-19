-- Prove2me | solution 1 for CohnElkies.saddleSourceShellDerivative_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/8f8c04a4-cce4-4bde-a4d4-09315f7dd1e6

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (ε u : ℝ) :
    saddleSourceShellDerivative ε (-u) =
      -saddleSourceShellDerivative ε u := by
  unfold saddleSourceShellDerivative
  have hshort :
      (∫ a in shortCutoff ε..shortEndpoint ε,
        shortShellDensity ε a * a *
          Real.sinh (-u * a)) =
        -(∫ a in shortCutoff ε..shortEndpoint ε,
          shortShellDensity ε a * a *
            Real.sinh (u * a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      shortShellDensity ε a * a * Real.sinh (-u * a) =
        -(shortShellDensity ε a * a * Real.sinh (u * a))
    rw [neg_mul, Real.sinh_neg]
    ring
  have hpositive :
      (∫ a in shellLocation ε..shellLocation ε + 1,
        positiveShellDensity ε a * a *
          Real.sinh (-u * a)) =
        -(∫ a in shellLocation ε..shellLocation ε + 1,
          positiveShellDensity ε a * a *
            Real.sinh (u * a)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro a ha
    change
      positiveShellDensity ε a * a * Real.sinh (-u * a) =
        -(positiveShellDensity ε a * a * Real.sinh (u * a))
    rw [neg_mul, Real.sinh_neg]
    ring
  rw [hshort, hpositive]
  ring
end CohnElkies
