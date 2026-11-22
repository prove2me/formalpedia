-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:35.747671+00:00
-- url     : https://prove2.me/submissions/691d45d8-bb77-4a44-a9be-6354c9b3862e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_lt_two_pow


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (u : Cube n) : cubeToNat u < 2 ^ n := by
  exact cubeToNat_lt_two_pow (fun i _ => i.isLt)
end BooleanIsoperimetry
