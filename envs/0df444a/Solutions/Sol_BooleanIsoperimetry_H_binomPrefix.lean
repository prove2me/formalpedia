-- Prove2me | solution 1 for BooleanIsoperimetry.H_binomPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:30.272246+00:00
-- url     : https://prove2.me/submissions/d497bccf-3b1f-4984-be98-36e37acab429

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_H_full
public import Theorems.Thm_BooleanIsoperimetry_H_one
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_eq_two_pow_of_ge
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pascal
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n r : ℕ) (hr : 1 ≤ r) :
    H n (binomPrefix n r) = binomPrefix n (r + 1) := by
  induction n generalizing r with
  | zero =>
      rw [binomPrefix_eq_two_pow_of_ge 0 r (by omega),
          binomPrefix_eq_two_pow_of_ge 0 (r + 1) (by omega),
          H_full]
  | succ n ih =>
      by_cases hrn : r ≤ n + 1
      · have hcasc := cascade_split_binomPrefix n r hr hrn
        rw [H_succ_cascade hcasc]
        by_cases hr_one : r = 1
        · subst r
          have hbp1 : binomPrefix n 1 = 1 := by
            simp [binomPrefix_succ, binomPrefix_zero]
          rw [hbp1, binomPrefix_zero, H_one, H_zero]
          simp [binomPrefix_succ, binomPrefix_zero, binomPrefix_pascal]
          omega
        · have hr_pred : 1 ≤ r - 1 := by omega
          have hHr := ih r hr
          have hHpred := ih (r - 1) hr_pred
          rw [hHr, hHpred]
          rw [show r - 1 + 1 = r by omega]
          have hmono₁ : binomPrefix n (r - 1) ≤ binomPrefix n (r + 1) :=
            binomPrefix_mono n (by omega)
          rw [max_eq_left hmono₁, max_eq_left (le_rfl : binomPrefix n r ≤ binomPrefix n r)]
          rw [binomPrefix_pascal n (r + 1)]
          rw [show r + 1 - 1 = r by omega]
      · have hfull : binomPrefix (n + 1) r = 2 ^ (n + 1) :=
          binomPrefix_eq_two_pow_of_ge (n + 1) r (by omega)
        have hfull_next : binomPrefix (n + 1) (r + 1) = 2 ^ (n + 1) :=
          binomPrefix_eq_two_pow_of_ge (n + 1) (r + 1) (by omega)
        rw [hfull, hfull_next, H_full]
end BooleanIsoperimetry
