-- Prove2me | solution 1 for FairSelling.three_MMS_le_vbarSum_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:32:09.198627+00:00
-- url     : https://prove2.me/submissions/2c704a76-aeae-45f3-84ad-5724f6551f59

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_ThreeAgents
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_exists_MMS_partition

attribute [local simp] FairSelling.restrictVal_mem

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g) :
    3 * MMS 3 w p ≤ vbarSum w p Finset.univ := by
  classical
  obtain ⟨o, hovalid, _hcover, hge⟩ := exists_MMS_partition (n := 3) (by norm_num) w p hw hp
  obtain ⟨hsold, hdisj, hmoney, hbudget⟩ := hovalid
  set U : Finset G := Finset.univ.biUnion o.kept with hU
  have hsum_ge : 3 * MMS 3 w p ≤ ∑ j, util w o j := by
    have hcst : ∑ _j : Fin 3, MMS 3 w p ≤ ∑ j, util w o j :=
      Finset.sum_le_sum (fun j _ => hge j)
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using hcst
  have hsum_eq : ∑ j, util w o j = (∑ g ∈ U, w g) + ∑ j, o.money j := by
    unfold util
    rw [Finset.sum_add_distrib]
    congr 1
    rw [hU, Finset.sum_biUnion]
    intro i _ j _ hij; exact hdisj i j hij
  have hUdisj : Disjoint U o.sold := by
    rw [hU, Finset.disjoint_biUnion_left]
    intro i _; exact (hsold i).symm
  have hbound : (∑ g ∈ U, w g) + ∑ j, o.money j ≤ vbarSum w p Finset.univ := by
    have h1 : (∑ g ∈ U, w g) ≤ ∑ g ∈ U, vbar w p g :=
      Finset.sum_le_sum (fun g _ => le_max_right _ _)
    have h2 : ∑ j, o.money j ≤ ∑ g ∈ o.sold, vbar w p g :=
      le_trans hbudget (Finset.sum_le_sum (fun g _ => le_max_left _ _))
    have h3 : (∑ g ∈ U, vbar w p g) + ∑ g ∈ o.sold, vbar w p g
        = ∑ g ∈ U ∪ o.sold, vbar w p g := (Finset.sum_union hUdisj).symm
    have h4 : ∑ g ∈ U ∪ o.sold, vbar w p g ≤ vbarSum w p Finset.univ := by
      unfold vbarSum
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun g _ _ => le_max_of_le_left (hp g))
    calc (∑ g ∈ U, w g) + ∑ j, o.money j
        ≤ (∑ g ∈ U, vbar w p g) + ∑ g ∈ o.sold, vbar w p g := by linarith
      _ = ∑ g ∈ U ∪ o.sold, vbar w p g := h3
      _ ≤ vbarSum w p Finset.univ := h4
  rw [hsum_eq] at hsum_ge
  exact le_trans hsum_ge hbound
end FairSelling
