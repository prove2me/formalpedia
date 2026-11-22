-- Prove2me | solution 1 for BooleanIsoperimetry.harper_gt_shadow_window_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:44:51.217281+00:00
-- url     : https://prove2.me/submissions/504261ff-7363-4965-85ea-f37f5f03ce7c

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_left_window_endpoints
public import Theorems.Thm_BooleanIsoperimetry_harper_gt_split_between


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n a b p q : ℕ}
    (hcasc : CascadeSplit (n + 1) (a + b) p q)
    (hq_pos : 1 ≤ q) (hcase : H (n + 1) b < a) :
    b ≤ q ∧ q ≤ p ∧ p ≤ a ∧ a - p = q - b := by
  obtain ⟨hbq, hqp, hpa⟩ := harper_gt_split_between n hq_pos hcase hcasc
  have hlen := cascade_left_window_endpoints hcasc hpa
  exact ⟨hbq, hqp, hpa, hlen.2⟩
end BooleanIsoperimetry
