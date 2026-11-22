-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLt_embed1_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:24.046623+00:00
-- url     : https://prove2.me/submissions/cb8463c3-70cd-4d46-a126-f04652c28e3f

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_embed1_card
public import Theorems.Thm_BooleanIsoperimetry_embed1_cubeToNat


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (u w : Cube n) :
    simplicialLt (embed1 u) (embed1 w) ↔ simplicialLt u w := by
  unfold simplicialLt simplicialLe
  rw [embed1_card, embed1_card, embed1_cubeToNat, embed1_cubeToNat]
  omega
end BooleanIsoperimetry
