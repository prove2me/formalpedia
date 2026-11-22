-- Prove2me | solution 1 for BooleanIsoperimetry.H_shadow_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:40:05.718908+00:00
-- url     : https://prove2.me/submissions/ef4f530b-7a3c-409a-b0d0-f701cde7c8cb

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
public import Theorems.Thm_BooleanIsoperimetry_H_binomPrefix
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (N r t : ℕ) (hr : 1 ≤ r) :
    H N (binomPrefix N r + t) = binomPrefix N (r + 1) + upperShadow N r t := by
  unfold upperShadow
  have hbase : H N (binomPrefix N r) = binomPrefix N (r + 1) := H_binomPrefix N r hr
  have hmono : H N (binomPrefix N r) ≤ H N (binomPrefix N r + t) :=
    H_mono (Nat.le_add_right _ _)
  omega
end BooleanIsoperimetry
