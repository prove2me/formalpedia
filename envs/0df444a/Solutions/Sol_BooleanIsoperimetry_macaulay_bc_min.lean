-- Prove2me | solution 1 for BooleanIsoperimetry.macaulay_bc_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:51:26.674347+00:00
-- url     : https://prove2.me/submissions/acd353d1-209e-4692-8783-76c760369499

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_MacaulayMin
public import Theorems.Thm_BooleanIsoperimetry_macaulay_extremal_pos_step
public import Theorems.Thm_BooleanIsoperimetry_H_zero
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_comm
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    max (H n p) q + max (H n q) p ≤ max (H n a) b + max (H n b) a := by
  by_cases hq_pos : 1 ≤ q
  · exact macaulay_extremal_pos_step n ih ha hb hp hq hpq hcasc hq_pos
  · push Not at hq_pos
    have hq0 : q = 0 := by omega
    subst hq0
    have hmax1 : max (H n p) 0 = H n p := max_eq_left (Nat.zero_le _)
    have hmax2 : max (H n 0) p = p := by rw [H_zero n]; exact max_eq_right (Nat.zero_le _)
    rw [hmax1, hmax2]
    cases le_total b a with
    | inl hb_le_a =>
      have hpq_zero : p = a + b := by omega
      exact harper_bc_min_q_zero_core n ha hb hp hb_le_a hpq_zero hcasc
    | inr ha_le_b =>
      rw [boundaryCost_comm n a b]
      have hcasc_symm : CascadeSplit n (b + a) p 0 := by simpa [Nat.add_comm] using hcasc
      have hpq_zero : p = b + a := by omega
      exact harper_bc_min_q_zero_core n hb ha hp ha_le_b hpq_zero hcasc_symm
end BooleanIsoperimetry
