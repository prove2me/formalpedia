-- Prove2me | solution 1 for BooleanIsoperimetry.harper_split_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:12.26407+00:00
-- url     : https://prove2.me/submissions/24ec5a29-ef3d-4224-b9aa-f7031b14e124

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
public import Theorems.Thm_BooleanIsoperimetry_H_exchange_max_form
public import Theorems.Thm_BooleanIsoperimetry_H_succ_cascade
public import Theorems.Thm_BooleanIsoperimetry_exists_cascade_split


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x y : ℕ} (hx : x ≤ 2 ^ n) (hy : y ≤ 2 ^ n) :
    H (n + 1) (x + y) ≤ max (H n x) y + max (H n y) x := by
  have hcasc := exists_cascade_split n (x + y) (by omega)
  rcases hcasc with ⟨p, q, _, _, hpq_sum, hpq⟩
  have h_H := H_succ_cascade hpq
  rw [h_H]
  exact H_exchange_max_form hpq hx hy rfl
end BooleanIsoperimetry
