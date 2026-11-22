-- Prove2me | solution 1 for BooleanIsoperimetry.H_exchange_max_form_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:38:28.628826+00:00
-- url     : https://prove2.me/submissions/7f24954c-6eff-48d7-885c-6428045df91d

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
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b p : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) (hp : p ≤ 2 ^ N)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit N (a + b) p 0) :
    H N p + p ≤ max (H N a) b + max (H N b) a :=
  harper_bc_min_q_zero_core N ha hb hp hb_le_a hpq hcasc
end BooleanIsoperimetry
