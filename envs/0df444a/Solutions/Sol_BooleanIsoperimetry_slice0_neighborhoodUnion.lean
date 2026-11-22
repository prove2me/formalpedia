-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_neighborhoodUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:53.069586+00:00
-- url     : https://prove2.me/submissions/18a05003-cf22-44be-88cd-6a74f12d4db6

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
public import Theorems.Thm_BooleanIsoperimetry_slice0_union
public import Theorems.Thm_BooleanIsoperimetry_slice0_simplicialInitSeg_eq_cascadeSplit
public import Theorems.Thm_BooleanIsoperimetry_slice1_simplicialInitSeg_eq_cascadeSplit
public import Theorems.Thm_BooleanIsoperimetry_cascade_upper_slice_subset_neighborhood_lower
public import Theorems.Thm_BooleanIsoperimetry_slice0_neighborhood


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N x y px qx py qy : ℕ}
    (hx : CascadeSplit N x px qx) (hy : CascadeSplit N y py qy) :
    slice0 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N px) ∪ simplicialInitSeg N py := by
  rw [slice0_union, slice0_neighborhood,
    slice0_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hx,
    slice0_simplicialInitSeg_eq_cascadeSplit hy]
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_left _
          (cascade_upper_slice_subset_neighborhood_lower hx hz)
    · exact Finset.mem_union_right _ hz
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    · exact Finset.mem_union_right _ hz
end BooleanIsoperimetry
