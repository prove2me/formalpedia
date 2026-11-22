-- Prove2me | solution 1 for BooleanIsoperimetry.HIncrement_le_of_mem_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:49.123819+00:00
-- url     : https://prove2.me/submissions/19e071e9-0249-4cca-9164-70647e58460c

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
public import Theorems.Thm_P2M_BooleanIsoperimetry_HIncrement_eq_min__d487d18fa7b9
public import Theorems.Thm_P2M_BooleanIsoperimetry_cube_min__add_card_le_534aca28a63b
public import Theorems.Thm_BooleanIsoperimetry_exists_rank_eq
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n r j : ℕ} (hr : 1 ≤ r)
    (hlo : binomPrefix n r ≤ j) (hhi : j < binomPrefix n (r + 1)) :
    HIncrement n j ≤ n - r := by
  have hj2 : j < 2 ^ n := lt_of_lt_of_le hhi (binomPrefix_le_two_pow n (r + 1))
  obtain ⟨w, hw⟩ := exists_rank_eq hj2
  have hcard_le : w.card ≤ r := by
    have := (rank_lt_binomPrefix_iff (c := r + 1) w).mp (by rw [hw]; exact hhi); omega
  have hcard_ge : r ≤ w.card := by
    by_contra hlt; push Not at hlt
    have : rank w < binomPrefix n r := (rank_lt_binomPrefix_iff (c := r) w).mpr hlt
    rw [hw] at this; omega
  have hcard : w.card = r := le_antisymm hcard_le hcard_ge
  have hne : w.Nonempty := by rw [← Finset.card_pos, hcard]; omega
  rw [HIncrement_eq_min' j w hw hne]
  have hmc := cube_min'_add_card_le w hne; omega
end BooleanIsoperimetry
