-- Prove2me | solution 1 for BooleanIsoperimetry.H_pair_step_forward_of_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:45:01.84884+00:00
-- url     : https://prove2.me/submissions/8f72990e-3857-4903-ada8-d6fa330db280

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_H_window_sum_of_le
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N x y : ℕ)
    (hy : 1 ≤ y) (hinc : HIncrement N (y - 1) ≤ HIncrement N x) :
    H N x + H N y ≤ H N (x + 1) + H N (y - 1) := by
  have hxwin := H_window_sum_of_le N x (x + 1) (by omega)
  have hywin := H_window_sum_of_le N (y - 1) y (by omega)
  have hxico : (∑ i ∈ Finset.Ico x (x + 1), HIncrement N i) = HIncrement N x := by
    simp
  have hyico :
      (∑ i ∈ Finset.Ico (y - 1) y, HIncrement N i) = HIncrement N (y - 1) := by
    have hy_eq : y = (y - 1) + 1 := by omega
    rw [hy_eq]
    simp
  rw [hxico] at hxwin
  rw [hyico] at hywin
  omega
end BooleanIsoperimetry
