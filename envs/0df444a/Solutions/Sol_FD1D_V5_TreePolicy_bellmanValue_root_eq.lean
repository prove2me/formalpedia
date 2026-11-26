-- Prove2me | solution 1 for FD1D.V5.TreePolicy.bellmanValue_root_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:25.731029+00:00
-- url     : https://prove2.me/submissions/bb5c2b73-ce83-4d03-9463-43aa9b4b75ad

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_root
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_root
attribute [local simp] FD1D.V5.TreePolicy.rate_leftChild
attribute [local simp] FD1D.V5.TreePolicy.rate_rightChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_root
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_leftChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_rightChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m) :
    bellmanValue I a 0 dyadicRoot =
      -1 / (2 * (m : ℝ) * ((m : ℝ) + a / 2)) := by
  rw [bellmanValue, discrepancy_root I ha hm, rate_root]
  simp only [bellman, zero_sub, zero_pow, Nat.ofNat_pos, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, div_zero, sub_zero]
  unfold regularizedMass intervalMass inventory
  rw [I.count_root]
  simp only [nodeMass_root, Nat.cast_ofNat]
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne']
  ring
end FD1D.V5.TreePolicy
