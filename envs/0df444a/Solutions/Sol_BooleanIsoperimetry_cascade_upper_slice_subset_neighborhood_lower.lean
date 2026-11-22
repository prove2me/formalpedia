-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_upper_slice_subset_neighborhood_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:25.676708+00:00
-- url     : https://prove2.me/submissions/76474680-8875-46ad-b9b2-b6085968ad4f

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
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le_p
public import Theorems.Thm_BooleanIsoperimetry_initSeg_nested
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N x p q : ℕ}
    (h : CascadeSplit N x p q) :
    simplicialInitSeg N q ⊆ neighborhood 1 (simplicialInitSeg N p) := by
  intro z hz
  have hqp : q ≤ p := cascade_q_le_p h
  have hz_p : z ∈ simplicialInitSeg N p := initSeg_nested hqp hz
  rw [mem_neighborhood_iff]
  exact ⟨z, hz_p, by simp [hDist]⟩
end BooleanIsoperimetry
