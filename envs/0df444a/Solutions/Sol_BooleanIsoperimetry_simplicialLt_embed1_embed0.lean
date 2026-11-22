-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLt_embed1_embed0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:41.368843+00:00
-- url     : https://prove2.me/submissions/b6eab886-a14a-4b54-b4f7-66957156bbdf

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_lt
public import Theorems.Thm_BooleanIsoperimetry_embed0_card
public import Theorems.Thm_BooleanIsoperimetry_embed0_cubeToNat
public import Theorems.Thm_BooleanIsoperimetry_embed1_card
public import Theorems.Thm_BooleanIsoperimetry_embed1_cubeToNat


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed0 w) ↔ u.card + 1 ≤ w.card := by
  have h0 := cubeToNat_lt w
  unfold simplicialLt simplicialLe
  rw [embed1_card, embed0_card, embed1_cubeToNat, embed0_cubeToNat]
  omega
end BooleanIsoperimetry
