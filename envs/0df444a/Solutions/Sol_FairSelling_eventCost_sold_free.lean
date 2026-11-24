-- Prove2me | solution 1 for FairSelling.eventCost_sold_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:12:05.389129+00:00
-- url     : https://prove2.me/submissions/6ff72854-5e65-4239-8b09-57993ef6079b

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
theorem _root_.solution (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) (f : G)
    (hfp : ∀ j, f ∉ E.part j) (hfs : f ∉ E.sell) (c : ℝ) :
    eventCost E A {f} c ≤ vbarSum w p A - p f + c := by
  classical
  have h1 : ∀ j, E.part j ∩ (A ∪ {f}) = E.part j ∩ A := by
    intro j
    rw [Finset.inter_union_distrib_left, Finset.inter_singleton_of_notMem (hfp j),
      Finset.union_empty]
  have h2 : E.sell ∩ (A ∪ {f}) = E.sell ∩ A := by
    rw [Finset.inter_union_distrib_left, Finset.inter_singleton_of_notMem hfs,
      Finset.union_empty]
  have h3 := event_goods_le E hp A
  simp only [eventCost, h2, Finset.sum_singleton,
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => congrArg (vbarSum w p) (h1 j))]
  simp only [vbarSum] at h3 ⊢
  linarith
end FairSelling
