-- Prove2me | solution 1 for BooleanIsoperimetry.harper_extremal_step_nested_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:57:45.690685+00:00
-- url     : https://prove2.me/submissions/9ea3b627-4c98-4e11-bcb4-15fbb86754cf

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
public import Theorems.Thm_BooleanIsoperimetry_harper_step_total
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split
public import Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested_q_zero


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ} (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q) :
    H (n + 1) p + H (n + 1) q ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  by_cases hq_zero : q = 0
  · have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    obtain ⟨p0, p1, hp0, hp1, _hp_add, hp_split⟩ := exists_cascade_split n p hp
    obtain ⟨q0, q1, hq0, hq1, _hq_add, hq_split⟩ := exists_cascade_split n q hq
    obtain ⟨a0, a1, ha0, ha1, _ha_add, ha_split⟩ := exists_cascade_split n a ha
    obtain ⟨b0, b1, hb0, hb1, _hb_add, hb_split⟩ := exists_cascade_split n b hb
    have hzero :=
      harper_extremal_step_nested_q_zero n ih ha hb hcasc hq_zero
        hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
        hp_split hq_split ha_split hb_split
    rw [H_succ_cascade hp_split, H_succ_cascade hq_split,
      H_succ_cascade ha_split, H_succ_cascade hb_split]
    exact le_trans (Nat.add_le_add (le_max_left _ _) (le_max_left _ _)) hzero
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
    have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
    have htotal := harper_step_total n ih ha hb
    have hsucc := H_succ_cascade hcasc
    have hcanon := canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc
    rw [hsucc, hcanon] at htotal
    exact htotal
end BooleanIsoperimetry
