-- Prove2me | solution 1 for FairSelling.event_goods_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:10:57.440421+00:00
-- url     : https://prove2.me/submissions/37c5dd7e-4cb1-4f46-b3d6-0c695ad09a03

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsBudget
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


section
open scoped BigOperators
namespace FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
section Cost
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G] in
/-- The contribution of a single good to the cost of an event that takes it away without selling
it is at most its `v̄`-value, and it is `0` unless the good belongs to a part or to the sell
set. -/
private lemma good_cost_kept (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g)
    (g : G) :
    (∑ j, if g ∈ E.part j then vbar w p g else 0) + (if g ∈ E.sell then p g else 0)
      ≤ vbar w p g := by
  classical
  by_cases hs : g ∈ E.sell
  · have hnp : ∀ j, g ∉ E.part j := fun j hj => Finset.disjoint_left.mp (E.sell_disj j) hs hj
    simp only [if_neg (hnp _), Finset.sum_const_zero, zero_add, if_pos hs]
    exact le_max_left _ _
  · simp only [if_neg hs, add_zero]
    by_cases hj : ∃ j, g ∈ E.part j
    · obtain ⟨j₀, hj₀⟩ := hj
      have hzero : ∀ j ∈ Finset.univ, j ≠ j₀ → (if g ∈ E.part j then vbar w p g else 0) = 0 := by
        intro j _ hne
        rw [if_neg (fun h => Finset.disjoint_left.mp (E.part_disj j j₀ hne) h hj₀)]
      rw [Finset.sum_eq_single j₀ hzero (fun h => absurd (Finset.mem_univ j₀) h), if_pos hj₀]
    · push_neg at hj
      simp only [hj, if_false, Finset.sum_const_zero]
      exact le_trans (hp g) (le_max_left _ _)
end Cost
end FairSelling
end

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable {w p : G → ℝ} {μ : ℝ} {k : ℕ}
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (E : EquiMMS w p μ k) (hp : ∀ g, 0 ≤ p g) (A : Finset G) :
    (∑ j, vbarSum w p (E.part j ∩ A)) + (∑ g ∈ E.sell ∩ A, p g) ≤ ∑ g ∈ A, vbar w p g := by
  classical
  have h1 : (∑ j, vbarSum w p (E.part j ∩ A))
      = ∑ j, ∑ g ∈ A, (if g ∈ E.part j then vbar w p g else 0) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [vbarSum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x; simp [Finset.mem_inter, and_comm]
  have h2 : (∑ g ∈ E.sell ∩ A, p g) = ∑ g ∈ A, (if g ∈ E.sell then p g else 0) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext x; simp [Finset.mem_inter, and_comm]
  rw [h1, h2]
  calc (∑ j, ∑ g ∈ A, (if g ∈ E.part j then vbar w p g else 0))
        + ∑ g ∈ A, (if g ∈ E.sell then p g else 0)
      = ∑ g ∈ A, ((∑ j, if g ∈ E.part j then vbar w p g else 0)
          + (if g ∈ E.sell then p g else 0)) := by
        rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    _ ≤ ∑ g ∈ A, vbar w p g :=
        Finset.sum_le_sum (fun g _ => good_cost_kept E hp g)
end FairSelling
