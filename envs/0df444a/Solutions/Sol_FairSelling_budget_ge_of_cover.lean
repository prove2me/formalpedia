-- Prove2me | solution 1 for FairSelling.budget_ge_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:13:20.902523+00:00
-- url     : https://prove2.me/submissions/952df13e-b032-4287-9bdf-b14a3d7ccb03

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_sum_split_cover
import Theorems.Thm_FairSelling_EquiMMS_budget_univ
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
namespace FairSelling
theorem _root_.solution {w p : G → ℝ} {μ : ℝ} (E : EquiMMS w p μ n) (R : Finset G) (D : ℝ)
    (alloc sold : Fin n → Finset G) (paid : Fin n → ℝ)
    (hdisj2 : ∀ b b', b ≠ b' → Disjoint (alloc b ∪ sold b) (alloc b' ∪ sold b'))
    (hdisjR : ∀ b, Disjoint R (alloc b ∪ sold b))
    (hcover : (Finset.univ : Finset G) = R ∪ Finset.univ.biUnion (fun b => alloc b ∪ sold b))
    (hmoney : (∑ b, ∑ g ∈ sold b, p g) - ∑ b, paid b ≤ D) :
    (n : ℝ) * μ - ∑ b, eventCost E (alloc b) (sold b) (paid b) ≤ E.budget R D := by
  classical
  set Gb : Fin n → Finset G := fun b => alloc b ∪ sold b with hGb
  -- split the budget along the state decomposition
  have hpart : ∀ j, vbarSum w p (E.part j)
      = vbarSum w p (E.part j ∩ R) + ∑ b, vbarSum w p (E.part j ∩ Gb b) := by
    intro j
    simpa [vbarSum] using
      sum_split_cover (E.part j) R Gb hcover hdisjR hdisj2 (f := fun g => vbar w p g)
  have hsell : (∑ g ∈ E.sell, p g)
      = (∑ g ∈ E.sell ∩ R, p g) + ∑ b, ∑ g ∈ E.sell ∩ Gb b, p g :=
    sum_split_cover E.sell R Gb hcover hdisjR hdisj2 (f := p)
  -- the budget before anything was allocated
  have htotal : (∑ j, vbarSum w p (E.part j)) + (∑ g ∈ E.sell, p g)
      = (n : ℝ) * μ := by
    have := E.budget_univ
    simpa [EquiMMS.budget] using this
  -- the budget now, in terms of the event costs
  have hcost : ∑ b, eventCost E (alloc b) (sold b) (paid b)
      = (∑ b, ((∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ g ∈ E.sell ∩ Gb b, p g))
        - (∑ b, ∑ g ∈ sold b, p g) + ∑ b, paid b := by
    simp only [eventCost, hGb]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have hsum1 : ∑ j, vbarSum w p (E.part j)
      = (∑ j, vbarSum w p (E.part j ∩ R))
        + ∑ b, ∑ j, vbarSum w p (E.part j ∩ Gb b) := by
    rw [Finset.sum_congr rfl (fun j _ => hpart j), Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hcost, EquiMMS.budget]
  rw [hsum1, hsell] at htotal
  have hsplitsum : ∑ b, ((∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ g ∈ E.sell ∩ Gb b, p g)
      = (∑ b, ∑ j, vbarSum w p (E.part j ∩ Gb b)) + ∑ b, ∑ g ∈ E.sell ∩ Gb b, p g :=
    Finset.sum_add_distrib
  rw [hsplitsum]
  linarith [hmoney]
end FairSelling
