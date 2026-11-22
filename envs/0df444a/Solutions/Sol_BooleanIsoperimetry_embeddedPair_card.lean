-- Prove2me | solution 1 for BooleanIsoperimetry.embeddedPair_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:19.910799+00:00
-- url     : https://prove2.me/submissions/9f7aa070-dddb-4b29-a4dd-fecc13b2d482

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
public import Theorems.Thm_BooleanIsoperimetry_compression_embed0_injective
public import Theorems.Thm_BooleanIsoperimetry_compression_embed1_injective
public import Theorems.Thm_BooleanIsoperimetry_disjoint_embeddedPair

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A B : Finset (Cube N)) :
    (embeddedPair N A B).card = A.card + B.card := by
  unfold embeddedPair
  rw [Finset.card_union_of_disjoint (disjoint_embeddedPair A B)]
  rw [Finset.card_image_of_injective _ compression_embed0_injective,
      Finset.card_image_of_injective _ compression_embed1_injective]
end BooleanIsoperimetry
