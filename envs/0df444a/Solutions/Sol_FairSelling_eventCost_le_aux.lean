-- Prove2me | solution 1 for FairSelling.eventCost_le_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:12:47.169658+00:00
-- url     : https://prove2.me/submissions/8a69fbe3-4f7f-4eba-8348-0cb66852ca3a

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_event_goods_le
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (Ea Fa : Finset G) (hEF : Disjoint Ea Fa) (c : ℝ) :
    eventCost E Ea Fa c ≤ vbarSum w p Ea + (∑ g ∈ Fa, (vbar w p g - p g)) + c := by
  classical
  have hsplit := event_goods_le E hp
  -- split the event's goods into those handed out and those sold
  have hunion : ∀ (F : G → ℝ), ∑ g ∈ Ea ∪ Fa, F g = (∑ g ∈ Ea, F g) + ∑ g ∈ Fa, F g :=
    fun F => Finset.sum_union hEF
  have hE1 : ∀ j, vbarSum w p (E.part j ∩ (Ea ∪ Fa))
      = vbarSum w p (E.part j ∩ Ea) + vbarSum w p (E.part j ∩ Fa) := by
    intro j
    rw [Finset.inter_union_distrib_left, vbarSum, vbarSum, vbarSum]
    exact Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))
  have hS1 : (∑ g ∈ E.sell ∩ (Ea ∪ Fa), p g)
      = (∑ g ∈ E.sell ∩ Ea, p g) + ∑ g ∈ E.sell ∩ Fa, p g := by
    rw [Finset.inter_union_distrib_left]
    exact Finset.sum_union (Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hEF))
  have hEa := hsplit Ea
  have hFa := hsplit Fa
  simp only [eventCost, hS1, Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hE1 j)]
  have hFsum : ∑ g ∈ Fa, (vbar w p g - p g) = (∑ g ∈ Fa, vbar w p g) - ∑ g ∈ Fa, p g := by
    rw [Finset.sum_sub_distrib]
  rw [hFsum]
  simp only [vbarSum] at hEa hFa ⊢
  linarith
end FairSelling
