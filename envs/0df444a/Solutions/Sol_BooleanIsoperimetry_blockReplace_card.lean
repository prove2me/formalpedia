-- Prove2me | solution 1 for BooleanIsoperimetry.blockReplace_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:24:41.15481+00:00
-- url     : https://prove2.me/submissions/07d808d9-7542-428f-8f5a-906ef8b5ce92

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

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N} {U V S : Cube N} (hUS : U ⊆ S) (hVS : Disjoint V S) :
    (blockReplace U V S).card = S.card - U.card + V.card := by
  unfold blockReplace
  rw [Finset.card_union_of_disjoint (Disjoint.disjoint_sdiff_left (Disjoint.symm hVS)),
    Finset.card_sdiff_of_subset hUS]
end BooleanIsoperimetry
