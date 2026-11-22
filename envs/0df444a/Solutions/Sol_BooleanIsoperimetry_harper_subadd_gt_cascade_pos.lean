-- Prove2me | solution 1 for BooleanIsoperimetry.harper_subadd_gt_cascade_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T08:01:24.910015+00:00
-- url     : https://prove2.me/submissions/c738322b-41df-4297-8ed5-cae32d4fedf7

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
public import Theorems.Thm_BooleanIsoperimetry_harper_subadd_gt_cascade_pos_succ_nested
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n : ℕ)
    (ih : ∀ m, m < n → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ n) (hb : b ≤ 2 ^ n) (hp : p ≤ 2 ^ n) (hq : q ≤ 2 ^ n)
    (hq_pos : 1 ≤ q)
    (hb_le_a : b ≤ a) (hcase : H n b < a)
    (hpq : p + q = a + b) (hcasc : CascadeSplit n (a + b) p q) :
    H n p + H n q ≤ H n a + a := by
  rcases n with _ | n
  · have hq_eq : q = 1 := by omega
    have hp_ge : q ≤ p := cascade_q_le_p hcasc
    have hp_eq : p = 1 := by omega
    have hab : a + b = 2 := by omega
    have ha_eq : a = 1 := by omega
    have hb_eq : b = 1 := by omega
    subst q
    subst p
    subst a
    subst b
    have hge : 1 ≤ H 0 1 := H_ge_self 0 1 (by norm_num)
    omega
  · obtain ⟨p0, p1, hp0, hp1, _, hp_split⟩ := exists_cascade_split n p hp
    obtain ⟨q0, q1, hq0, hq1, _, hq_split⟩ := exists_cascade_split n q hq
    obtain ⟨a0, a1, ha0, ha1, _, ha_split⟩ := exists_cascade_split n a ha
    obtain ⟨b0, b1, hb0, hb1, _, hb_split⟩ := exists_cascade_split n b hb
    have hcase' :
        max (H n b0) b1 + max (H n b1) b0 < a := by
      simpa [H_succ_cascade hb_split] using hcase
    have hnested :=
      harper_subadd_gt_cascade_pos_succ_nested n ih
        ha hb hp hq hq_pos hb_le_a hcase' hpq hcasc
        hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
        hp_split hq_split ha_split hb_split
    simpa [H_succ_cascade hp_split, H_succ_cascade hq_split,
      H_succ_cascade ha_split] using hnested
end BooleanIsoperimetry
