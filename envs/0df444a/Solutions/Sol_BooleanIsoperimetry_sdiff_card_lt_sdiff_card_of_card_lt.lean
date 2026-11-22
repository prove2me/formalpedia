-- Prove2me | solution 1 for BooleanIsoperimetry.sdiff_card_lt_sdiff_card_of_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:49.519714+00:00
-- url     : https://prove2.me/submissions/8dfab80b-7b35-449f-b47d-ae39441ae049

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
theorem _root_.solution {N : ℕ} {S T : Cube N}
    (hcard : T.card < S.card) : (T \ S).card < (S \ T).card := by
  have hTsplit : (T ∩ S).card + (T \ S).card = T.card :=
    Finset.card_inter_add_card_sdiff T S
  have hSsplit : (S ∩ T).card + (S \ T).card = S.card :=
    Finset.card_inter_add_card_sdiff S T
  have hcomm : (S ∩ T).card = (T ∩ S).card := by rw [Finset.inter_comm]
  omega
end BooleanIsoperimetry
