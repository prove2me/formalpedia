-- Prove2me | solution 1 for BooleanIsoperimetry.H_exchange_q_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:24.711602+00:00
-- url     : https://prove2.me/submissions/defb9255-3362-46ae-bcfd-8e2ceb4b7e4e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_harper_bc_min_q_zero_core


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N a b p : ℕ}
    (ha : a ≤ 2 ^ N) (hb : b ≤ 2 ^ N) (hp : p ≤ 2 ^ N)
    (hb_le_a : b ≤ a)
    (hpq : p = a + b) (hcasc : CascadeSplit N (a + b) p 0) :
    H N p + p ≤ max (H N a) b + max (H N b) a :=
  harper_bc_min_q_zero_core N ha hb hp hb_le_a hpq hcasc
end BooleanIsoperimetry
