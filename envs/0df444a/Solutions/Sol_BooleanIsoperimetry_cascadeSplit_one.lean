-- Prove2me | solution 1 for BooleanIsoperimetry.cascadeSplit_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:53.11749+00:00
-- url     : https://prove2.me/submissions/6331361a-6a62-41d6-bef7-51a78c9b6fb3

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n : ℕ) : CascadeSplit n 1 1 0 := by
  refine ⟨1, 0, ⟨by omega, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [Nat.choose]
  · simp [binomPrefix, Nat.choose]
  · exact Or.inl (by simp [Nat.choose])
  · simp [cascadeSlice0Value, binomPrefix, choosePred]
  · simp [cascadeSlice1Value, binomPrefix, choosePred]
end BooleanIsoperimetry
