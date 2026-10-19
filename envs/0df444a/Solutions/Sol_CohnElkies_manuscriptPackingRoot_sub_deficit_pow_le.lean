-- Prove2me | solution 1 for CohnElkies.manuscriptPackingRoot_sub_deficit_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/8643acca-5416-4112-aefe-24d9770bc83d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_linearProgram_nonneg
import Theorems.Thm_CohnElkies_manuscriptPackingDeficit_le_criticalPackingBase
import Theorems.Thm_CohnElkies_manuscriptPackingRoot_sub_deficit_le

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
    (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      linearProgram d := by
  have hbase : 0 ≤ criticalPackingBase - manuscriptPackingDeficit d :=
    sub_nonneg.mpr (manuscriptPackingDeficit_le_criticalPackingBase d)
  have hpower :=
    pow_le_pow_left₀ hbase (manuscriptPackingRoot_sub_deficit_le d) d
  rw [Real.rpow_inv_natCast_pow (linearProgram_nonneg d)
    (Nat.ne_of_gt hd)] at hpower
  exact hpower
end CohnElkies
