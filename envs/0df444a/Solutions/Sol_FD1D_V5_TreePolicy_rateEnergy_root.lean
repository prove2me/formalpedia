-- Prove2me | solution 1 for FD1D.V5.TreePolicy.rateEnergy_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:51:57.70404+00:00
-- url     : https://prove2.me/submissions/6cb5c468-b1ea-4dc4-905c-cf05ba8ddbde

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_hazardEnergy_root
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_root

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m) (a : ℝ)
    (hm : 0 < m) :
    hazardEnergy (rate I a) 0 = 1 / (m : ℝ) ^ 2 := by
  rw [hazardEnergy_root, rate_root]
  field_simp
end FD1D.V5.TreePolicy
