-- Prove2me | solution 1 for BooleanIsoperimetry.H_add_self_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:41:19.26389+00:00
-- url     : https://prove2.me/submissions/d1bac51e-e201-4206-8131-4b1ec3cc6fb5

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_H_mono


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n x y : ℕ} (h : x ≤ y) : H n x + x ≤ H n y + y :=
  Nat.add_le_add (H_mono h) h
end BooleanIsoperimetry
