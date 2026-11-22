-- Prove2me | solution 1 for BooleanIsoperimetry.harper_macaulay_shadow_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:54:45.405139+00:00
-- url     : https://prove2.me/submissions/e33fe6d9-2773-41fc-a3d1-b8104c35e041

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
public import Theorems.Thm_BooleanIsoperimetry_gShiftIntervalCount_eq_H_sub
public import Theorems.Thm_BooleanIsoperimetry_harper_macaulay_slack_gt
public import Theorems.Thm_BooleanIsoperimetry_H_mono
public import Theorems.Thm_BooleanIsoperimetry_harper_gt_split_between


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ)
    (ih : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    {a b p q : ℕ}
    (ha : a ≤ 2 ^ (n + 1)) (hb : b ≤ 2 ^ (n + 1))
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hba : b ≤ a) (hcase : H (n + 1) b < a) (hq_pos : 1 ≤ q) :
    gShiftIntervalCount (n + 1) b q ≤
      gShiftIntervalCount (n + 1) p a + (a - H (n + 1) b) := by
  obtain ⟨hbq, hqp, hpa⟩ := harper_gt_split_between n hq_pos hcase hcasc
  rw [gShiftIntervalCount_eq_H_sub (n + 1) b q hbq,
      gShiftIntervalCount_eq_H_sub (n + 1) p a hpa]
  have hslack := harper_macaulay_slack_gt n ih ha hb hcasc hq_pos hba hcase
  have hHbq : H (n + 1) b ≤ H (n + 1) q := H_mono hbq
  have hHpa : H (n + 1) p ≤ H (n + 1) a := H_mono hpa
  omega
end BooleanIsoperimetry
