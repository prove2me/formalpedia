-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialInitSeg_isFullyCompressed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:30.72849+00:00
-- url     : https://prove2.me/submissions/d576c1e4-e610-47e3-a586-53c1dea7cf20

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Definitions.Def_LeanPool_BooleanIsoperimetry_LayerWindows
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Mathlib.Combinatorics.SetFamily.Compression.UV
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Compression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_strictMono
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N m : ℕ} :
    IsFullyCompressed (simplicialInitSeg N m) := by
  constructor
  · -- lower level saturated
    intro x y hcard hy
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hlt : simplicialLt x y := by
      refine ⟨Or.inl hcard, ?_⟩
      simp only [simplicialLe, not_or]
      exact ⟨by omega, fun ⟨heq, _⟩ => by omega⟩
    exact lt_trans (rank_strictMono hlt) hy
  · -- colex shift fixed
    intro A' hshift
    obtain ⟨_, x, y, hx, hy, _, hlt, _⟩ := hshift
    simp only [simplicialInitSeg, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hy (lt_trans (rank_strictMono hlt) hx)
end BooleanIsoperimetry
