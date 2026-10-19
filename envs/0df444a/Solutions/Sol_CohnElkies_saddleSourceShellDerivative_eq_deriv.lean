-- Prove2me | solution 1 for CohnElkies.saddleSourceShellDerivative_eq_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/c22dfadc-8c08-4432-ac9a-f48233776eb3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_realHyperbolicShellPhase_hasDerivAt

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
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (u : ℝ) :
    saddleSourceShellDerivative ε u =
      deriv (realHyperbolicShellPhase ε) u := by
  have h :=
    (realHyperbolicShellPhase_hasDerivAt
      hε horder u).deriv
  unfold saddleSourceShellDerivative
  simpa [mul_comm] using! h.symm
end CohnElkies
