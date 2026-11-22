-- Prove2me | solution 1 for BooleanIsoperimetry.slice1_simplicialInitSeg_eq_cascadeSplit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:58.562772+00:00
-- url     : https://prove2.me/submissions/51a25206-65bd-4cf0-8ffa-bd14f63a3941

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
public import Theorems.Thm_BooleanIsoperimetry_slice1_initSeg_eq
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
    slice1 (simplicialInitSeg (N + 1) x) = simplicialInitSeg N q := by
  rw [slice1_initSeg_eq, (slice_card_eq_cascade h).2]
end BooleanIsoperimetry
