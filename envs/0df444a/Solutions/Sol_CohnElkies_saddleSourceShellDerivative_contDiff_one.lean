-- Prove2me | solution 1 for CohnElkies.saddleSourceShellDerivative_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/85c1a0e0-761b-471a-9bc3-69fb9ae0799f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_contDiff
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_eq_deriv

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
    {ε : ℝ} (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ContDiff ℝ (1 : WithTop ℕ∞)
      (saddleSourceShellDerivative ε) := by
  have hphase :
      ContDiff ℝ ((1 : WithTop ℕ∞) + 1)
        (realHyperbolicShellPhase ε) := by
    convert! realHyperbolicShellPhase_contDiff
      hε horder (2 : WithTop ℕ∞) using 1
  have hderiv :
      ContDiff ℝ (1 : WithTop ℕ∞)
        (deriv (realHyperbolicShellPhase ε)) :=
    (contDiff_succ_iff_deriv.mp hphase).2.2
  have heq :
      saddleSourceShellDerivative ε =
        deriv (realHyperbolicShellPhase ε) := by
    funext u
    exact saddleSourceShellDerivative_eq_deriv hε horder u
  rw [heq]
  exact hderiv
end CohnElkies
