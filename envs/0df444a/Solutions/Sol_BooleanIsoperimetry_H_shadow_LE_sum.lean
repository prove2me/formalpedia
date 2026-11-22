-- Prove2me | solution 1 for BooleanIsoperimetry.H_shadow_LE_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:49:26.533066+00:00
-- url     : https://prove2.me/submissions/6333fbfc-e56d-4b9b-aeac-291ea5c64afe

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
public import Theorems.Thm_BooleanIsoperimetry_boundaryCost_eq_case_le
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
    (hq_pos : 1 ≤ q) (hba : b ≤ a) (hcase : a ≤ H N b) :
    H N p + H N q ≤ H N a + H N b := by
  have hp : p ≤ 2 ^ N := cascade_p_le hcasc
  have hq : q ≤ 2 ^ N := cascade_q_le hcasc
  have hmax := H_exchange_max_form_pos hcasc ha hb hq_pos
  rw [canonical_boundaryCost_eq_H_add hp hq hq_pos hcasc,
      boundaryCost_eq_case_le ha hba hcase] at hmax
  exact hmax
end BooleanIsoperimetry
