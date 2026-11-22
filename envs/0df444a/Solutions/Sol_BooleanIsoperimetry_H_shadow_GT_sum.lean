-- Prove2me | solution 1 for BooleanIsoperimetry.H_shadow_GT_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:27.052699+00:00
-- url     : https://prove2.me/submissions/6216b56b-052e-455c-9505-0ed4e0be63f2

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
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_gt
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b p q : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N)
    (hcasc : CascadeSplit N (a + b) p q)
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : H N b < a) :
    H N p + H N q ≤ H N a + a := by
  have hp : p ≤ 2 ^ N := cascade_p_le hcasc
  have hq : q ≤ 2 ^ N := cascade_q_le hcasc
  have hmax := H_exchange_max_form_pos hcasc ha hb hq_pos
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc,
      boundaryCost_eq_case_gt ha hba hcase] at hmax
  exact hmax
end BooleanIsoperimetry
