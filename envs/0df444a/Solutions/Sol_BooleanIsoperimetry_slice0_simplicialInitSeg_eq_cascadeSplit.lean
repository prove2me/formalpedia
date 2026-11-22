-- Prove2me | solution 1 for BooleanIsoperimetry.slice0_simplicialInitSeg_eq_cascadeSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:57.400796+00:00
-- url     : https://prove2.me/submissions/efddf912-e773-4ff5-95e9-04357d405ad6

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
public import Theorems.Thm_BooleanIsoperimetry_slice0_initSeg_eq
public import Theorems.Thm_BooleanIsoperimetry_slice_card_eq_cascade


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N x p q : ℕ} (h : CascadeSplit N x p q) :
    slice0 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N p := by
  rw [slice0_initSeg_eq, (slice_card_eq_cascade h).1]
end BooleanIsoperimetry
