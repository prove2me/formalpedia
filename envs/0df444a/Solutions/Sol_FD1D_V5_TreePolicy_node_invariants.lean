-- Prove2me | solution 1 for FD1D.V5.TreePolicy.node_invariants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:08.597844+00:00
-- url     : https://prove2.me/submissions/bfec2a2e-e82c-4e47-ad47-2f83e172d264

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_root
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_eq_local
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_rightChild
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_child_invariants
import Theorems.Thm_FD1D_nodeMass_pos
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
    ∀ d, d ≤ L → ∀ v,
      0 < rate I a d v ∧
        discrepancy I a d v ≤ rate I a d v / 2 ∧
        regularizedMass I a d v ≤ rate I a d v := by
  intro d
  induction d with
  | zero =>
      intro _ v
      have hv : v = dyadicRoot := Fin.eq_zero v
      subst v
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
      have hrate : 0 < rate I a 0 dyadicRoot := by
        rw [rate_root]
        exact one_div_pos.mpr hmR
      have hdisc : discrepancy I a 0 dyadicRoot ≤
          rate I a 0 dyadicRoot / 2 := by
        rw [discrepancy_root I ha hm]
        positivity
      have hreg :
          regularizedMass I a 0 dyadicRoot ≤
            rate I a 0 dyadicRoot := by
        unfold regularizedMass inventory intervalMass
        rw [I.count_root]
        simp only [nodeMass_root, rate_root]
        apply one_div_le_one_div_of_le hmR
        have : 0 ≤ a / 2 := by positivity
        linarith
      exact ⟨hrate, hdisc, hreg⟩
  | succ d ih =>
      intro hdL w
      let z := (childrenEquiv d).symm w
      have hz : childrenEquiv d z = w :=
        (childrenEquiv d).apply_symm_apply w
      have hd : d < L := by omega
      have hp := ih (by omega) z.1
      let x := I.count (d + 1) (leftChild z.1)
      let y := I.count (d + 1) (rightChild z.1)
      have htLocal :
          LocalPolicy.discrepancy a (intervalMass d z.1)
              (rate I a d z.1) x y ≤
            rate I a d z.1 / 2 := by
        dsimp [x, y]
        rw [← discrepancy_eq_local I a d hd z.1]
        exact hp.2.1
      have hchildren :=
        LocalPolicy.child_invariants ha (nodeMass_pos d z.1)
          hp.1 htLocal
      have hZLpos :
          0 < regularizedMassLeft a (intervalMass d z.1) x y := by
        unfold regularizedMassLeft
        exact div_pos (div_pos (nodeMass_pos d z.1) (by norm_num))
          (by positivity)
      have hZRpos :
          0 < regularizedMassRight a (intervalMass d z.1) x y := by
        unfold regularizedMassRight
        exact div_pos (div_pos (nodeMass_pos d z.1) (by norm_num))
          (by positivity)
      rw [← hz]
      rcases z with ⟨v, side⟩
      fin_cases side
      · change
          0 < rate I a (d + 1) (leftChild v) ∧
            discrepancy I a (d + 1) (leftChild v) ≤
              rate I a (d + 1) (leftChild v) / 2 ∧
            regularizedMass I a (d + 1) (leftChild v) ≤
              rate I a (d + 1) (leftChild v)
        rw [rate_leftChild, discrepancy_leftChild,
          regularizedMass_leftChild]
        exact ⟨hZLpos.trans_le hchildren.2.1,
          hchildren.1, hchildren.2.1⟩
      · change
          0 < rate I a (d + 1) (rightChild v) ∧
            discrepancy I a (d + 1) (rightChild v) ≤
              rate I a (d + 1) (rightChild v) / 2 ∧
            regularizedMass I a (d + 1) (rightChild v) ≤
              rate I a (d + 1) (rightChild v)
        rw [rate_rightChild, discrepancy_rightChild,
          regularizedMass_rightChild]
        exact ⟨hZRpos.trans_le hchildren.2.2.2,
          hchildren.2.2.1, hchildren.2.2.2⟩
end FD1D.V5.TreePolicy
