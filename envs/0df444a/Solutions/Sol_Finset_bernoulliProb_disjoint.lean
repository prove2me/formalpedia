-- Prove2me | solution 1 for Finset.bernoulliProb_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:02.626207+00:00
-- url     : https://prove2.me/submissions/56265131-7da7-4d0c-ab65-51aa1cee4c19

module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Theorems.Thm_Finset_bernoulliWeight_sdiff
public import Theorems.Thm_Finset_bernoulliProb_superset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Finset
variable {α : Type*} [DecidableEq α] (U : Finset α) (p : ℝ)
variable {U p}
namespace Finset
theorem _root_.solution {F : Finset α} (hF : F ⊆ U) :
    U.bernoulliProb p (Disjoint · F) = (1 - p) ^ #F := by
  rw [← bernoulliProb_superset (p := 1 - p) hF, bernoulliProb, bernoulliProb]
  refine sum_nbij' (U \ ·) (U \ ·) (fun A hA => ?_) (fun A hA => ?_) (fun A hA => ?_)
    (fun A hA => ?_) fun A hA => ?_
  · obtain ⟨hAU, hAF⟩ := mem_filter.mp hA
    refine mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, fun x hx => mem_sdiff.mpr ⟨hF hx, ?_⟩⟩
    exact fun hxA => disjoint_left.mp hAF hxA hx
  · obtain ⟨hAU, hFA⟩ := mem_filter.mp hA
    refine mem_filter.mpr ⟨mem_powerset.mpr sdiff_subset, disjoint_left.mpr fun x hx hxF => ?_⟩
    exact (mem_sdiff.mp hx).2 (hFA hxF)
  · exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hA).1)
  · exact sdiff_sdiff_eq_self (mem_powerset.mp (mem_filter.mp hA).1)
  · rw [bernoulliWeight_sdiff (mem_powerset.mp (mem_filter.mp hA).1)]
end Finset
