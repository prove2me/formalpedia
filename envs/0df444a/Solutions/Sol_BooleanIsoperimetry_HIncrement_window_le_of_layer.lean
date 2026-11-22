-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_window_le_of_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:21.769589+00:00
-- url     : https://prove2.me/submissions/62661f87-e547-46b9-a1ef-909a3b0b1e4f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Theorems.Thm_BooleanIsoperimetry_HIncrement_le_of_mem_layer
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n r a L : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ a) (hhi : a + L ≤ binomPrefix n (r + 1)) :
    (∑ i ∈ Finset.Ico a (a + L), HIncrement n i) ≤ L * (n - r) := by
  have hbound : ∀ i ∈ Finset.Ico a (a + L), HIncrement n i ≤ n - r := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact HIncrement_le_of_mem_layer hr (le_trans hlo hi.1) (lt_of_lt_of_le hi.2 hhi)
  calc (∑ i ∈ Finset.Ico a (a + L), HIncrement n i)
      ≤ ∑ _i ∈ Finset.Ico a (a + L), (n - r) := Finset.sum_le_sum hbound
    _ = L * (n - r) := by rw [Finset.sum_const, Nat.card_Ico]; simp
end BooleanIsoperimetry
