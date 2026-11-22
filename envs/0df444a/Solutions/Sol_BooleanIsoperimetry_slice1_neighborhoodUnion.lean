-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_neighborhoodUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:53.457223+00:00
-- url     : https://prove2.me/submissions/f29f46cb-c020-4934-a4b2-df26709d415b

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
public import Theorems.Thm_BooleanIsoperimetry_slice1_union
public import Theorems.Thm_BooleanIsoperimetry_slice0_simplicialInitSeg_eq_cascadeSplit
public import Theorems.Thm_BooleanIsoperimetry_slice1_simplicialInitSeg_eq_cascadeSplit
public import Theorems.Thm_BooleanIsoperimetry_slice1_neighborhood


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
    slice1 (neighborhood 1 (simplicialInitSeg (N + 1) x) ∪ simplicialInitSeg (N + 1) y)
      = neighborhood 1 (simplicialInitSeg N qx) ∪ simplicialInitSeg N px ∪
          simplicialInitSeg N qy := by
  rw [slice1_union, slice1_neighborhood,
    slice0_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hx,
    slice1_simplicialInitSeg_eq_cascadeSplit hy]
end BooleanIsoperimetry
