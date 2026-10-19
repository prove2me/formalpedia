-- Prove2me | solution 1 for CohnElkies.upperPositiveShellVariance_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/c196a7ee-397c-48cc-b7b0-6aeb457ad409

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_bounds

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
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) :
    0 < upperPositiveShellVariance ε δ := by
  have hB : 0 < shellLocation ε := by
    unfold shellLocation
    positivity
  have hlower :=
    (upperPositiveShellVariance_bounds hε hδ).1
  have hpositive :
      0 < (1 / 2 : ℝ) *
        (shellLocation ε) ^ 2 *
          shellWeight ε *
            Real.exp (δ * shellLocation ε) := by
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num)
          (sq_pos_of_pos hB))
        (shellWeight_pos ε))
      (Real.exp_pos _)
  exact hpositive.trans_le hlower
end CohnElkies
