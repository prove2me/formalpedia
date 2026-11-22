-- Prove2me | solution 1 for BooleanIsoperimetry.initialSlicePair_embed1_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:32:08.781586+00:00
-- url     : https://prove2.me/submissions/8f3a4395-47be-4c4e-bc55-1bf70fed867a

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_initialSlicePair_last_not_mem_embed0
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} : Function.Injective (@embed1 N) := by
  intro x y h
  unfold embed1 at h
  have key : x.image Fin.castSucc = y.image Fin.castSucc := by
    have := congrArg (·.erase (Fin.last N)) h
    simpa [Finset.erase_insert, initialSlicePair_last_not_mem_embed0] using this
  exact Finset.image_injective (Fin.castSucc_injective N) key
end BooleanIsoperimetry
