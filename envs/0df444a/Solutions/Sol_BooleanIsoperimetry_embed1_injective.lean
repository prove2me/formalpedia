-- Prove2me | solution 1 for BooleanIsoperimetry.embed1_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:43.694098+00:00
-- url     : https://prove2.me/submissions/79e63eae-8e7d-4505-a13c-9ba686e3a020

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
public import Theorems.Thm_BooleanIsoperimetry_last_not_mem_image_castSucc
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} : Function.Injective (@embed1 n) := by
  intro x y h
  unfold embed1 at h
  have key : x.image Fin.castSucc = y.image Fin.castSucc := by
    have := congrArg (·.erase (Fin.last n)) h
    simpa [Finset.erase_insert, last_not_mem_image_castSucc] using this
  exact Finset.image_injective (Fin.castSucc_injective n) key
end BooleanIsoperimetry
