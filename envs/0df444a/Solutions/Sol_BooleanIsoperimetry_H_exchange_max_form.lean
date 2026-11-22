-- Prove2me | solution 1 for BooleanIsoperimetry.H_exchange_max_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:27.570792+00:00
-- url     : https://prove2.me/submissions/a114f141-50a2-4a9d-9455-7ab91184720d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Theorems.Thm_BooleanIsoperimetry_H_exchange_max_form_pos
public import Theorems.Thm_BooleanIsoperimetry_H_exchange_max_form_q_zero
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N s p q a b : ℕ}
    (hpq : CascadeSplit N s p q) (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hab : a + b = s) :
    max (H N p) q + max (H N q) p ≤ max (H N a) b + max (H N b) a := by
  subst hab
  have hp : p ≤ 2 ^ N := cascade_p_le hpq
  rcases eq_or_lt_of_le (Nat.zero_le q) with rfl | hq_pos
  · have h_LHS : max (H N p) 0 + max (H N 0) p = H N p + p := by
      rw [H_zero]
      exact congr_arg₂ (· + ·) (max_eq_left (Nat.zero_le _)) (max_eq_right (Nat.zero_le _))
    rw [h_LHS]
    rcases le_total b a with hba | hab'
    · have hp_eq : p = a + b := by
        have : p + 0 = a + b := cascade_split_add hpq
        omega
      have hcasc_0 : CascadeSplit N (a + b) p 0 := hpq
      exact H_exchange_max_form_q_zero ha hb hp hba hp_eq hcasc_0
    · rw [add_comm (max (H N a) b) (max (H N b) a)]
      have hp_eq : p = b + a := by
        have : p + 0 = a + b := cascade_split_add hpq
        omega
      have hcasc_0 : CascadeSplit N (b + a) p 0 := by
        rw [add_comm b a]; exact hpq
      exact H_exchange_max_form_q_zero hb ha hp hab' hp_eq hcasc_0
  · exact H_exchange_max_form_pos hpq ha hb hq_pos
end BooleanIsoperimetry
