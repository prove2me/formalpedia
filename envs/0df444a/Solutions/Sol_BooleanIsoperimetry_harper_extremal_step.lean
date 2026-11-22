-- Prove2me | solution 1 for BooleanIsoperimetry.harper_extremal_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:58:53.93181+00:00
-- url     : https://prove2.me/submissions/ac855139-81c0-46dc-b6a6-f42f95be20a1

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
public import Theorems.Thm_BooleanIsoperimetry_harper_extremal_step_nested
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


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
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  have hp : p ≤ 2 ^ (n + 1) := cascade_p_le hcasc
  have hq : q ≤ 2 ^ (n + 1) := cascade_q_le hcasc
  obtain ⟨p0, p1, hp0, hp1, _, hp_split⟩ := exists_cascade_split n p hp
  obtain ⟨q0, q1, hq0, hq1, _, hq_split⟩ := exists_cascade_split n q hq
  obtain ⟨a0, a1, ha0, ha1, _, ha_split⟩ := exists_cascade_split n a ha
  obtain ⟨b0, b1, hb0, hb1, _, hb_split⟩ := exists_cascade_split n b hb
  have h_nested := harper_extremal_step_nested n ih ha hb hcasc
    hp0 hp1 hq0 hq1 ha0 ha1 hb0 hb1
    hp_split hq_split ha_split hb_split
  rwa [← H_succ_cascade hp_split, ← H_succ_cascade hq_split,
       ← H_succ_cascade ha_split, ← H_succ_cascade hb_split] at h_nested
end BooleanIsoperimetry
