-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialLt_embed0_embed1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:24.447872+00:00
-- url     : https://prove2.me/submissions/39f90aee-ab74-4d01-90f8-b13db6804a2b

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
    simplicialLt (embed0 u) (embed1 w) ↔ u.card < w.card + 1 := by
  have h0 := cubeToNat_lt u
  unfold simplicialLt simplicialLe
  rw [embed0_card, embed1_card, embed0_cubeToNat, embed1_cubeToNat]
  omega
end BooleanIsoperimetry
