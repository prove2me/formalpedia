-- Prove2me | solution 1 for FD1D.V5.TreePolicy.deletionMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:57.495552+00:00
-- url     : https://prove2.me/submissions/b1c7060a-3a12-43ff-9c4f-d1bbe84a5c06

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_pos

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    0 ≤ deletionMass I a d v := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (rate_pos I ha hm hdL v).le
end FD1D.V5.TreePolicy
