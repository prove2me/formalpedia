-- Prove2me | solution 1 for FD1D.V5.TreePolicy.sum_deletionMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:00.498801+00:00
-- url     : https://prove2.me/submissions/9cbf6135-b48b-4baf-ad1e-59ab564685db

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_children
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_root
import Theorems.Thm_FD1D_CoherentTreeLabel_levelSum_eq_root


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    {a : ℝ} (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) :
    ∑ v, deletionMass I a d v = 1 := by
  let q : CoherentTreeLabel L ℝ :=
    { value := deletionMass I a
      children := deletionMass_children I a }
  rw [show (∑ v, deletionMass I a d v) = levelSum q.value d by rfl]
  rw [q.levelSum_eq_root hdL]
  exact deletionMass_root I a hm
end FD1D.V5.TreePolicy
