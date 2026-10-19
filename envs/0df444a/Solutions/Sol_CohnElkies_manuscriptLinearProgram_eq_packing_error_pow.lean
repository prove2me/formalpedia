-- Prove2me | solution 1 for CohnElkies.manuscriptLinearProgram_eq_packing_error_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/a77b9436-4f77-4f65-8d49-8162f06ba642

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_linearProgram_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) :
    linearProgram d =
      (criticalPackingBase + manuscriptPackingRootError d) ^ d := by
  have hroot :
      criticalPackingBase + manuscriptPackingRootError d =
        (linearProgram d) ^ ((d : ℝ)⁻¹) := by
    unfold manuscriptPackingRootError
    ring
  rw [hroot]
  exact (Real.rpow_inv_natCast_pow (linearProgram_nonneg d)
    (Nat.ne_of_gt hd)).symm
end CohnElkies
