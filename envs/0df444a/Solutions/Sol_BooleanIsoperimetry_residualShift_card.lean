-- Prove2me | solution 1 for BooleanIsoperimetry.residualShift_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:21.426277+00:00
-- url     : https://prove2.me/submissions/80813f4d-b92c-4578-9c8d-f1c6a4c9a85a

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
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)}
    (h : IsDownFixedResidualShift A A') : A'.card = A.card := h.1
end BooleanIsoperimetry
