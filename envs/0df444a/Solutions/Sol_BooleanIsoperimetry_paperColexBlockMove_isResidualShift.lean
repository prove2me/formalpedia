-- Prove2me | solution 1 for BooleanIsoperimetry.paperColexBlockMove_isResidualShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:23.168033+00:00
-- url     : https://prove2.me/submissions/578c2591-f3d5-41c9-9d81-df3575c28a70

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
public import Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_card
public import Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_neighborhood_card_le
public import Theorems.Thm_BooleanIsoperimetry_paperColexBlockMove_potential_lt

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A A' : Finset (Cube N)} {i j : Fin N}
    (h : IsPaperColexBlockMove A A' i j)
    (_hdown : IsCoordinateDownFixed A)
    (_hlower : IsLowerLevelSaturated A) : IsDownFixedResidualShift A A' :=
  ⟨paperColexBlockMove_card h, paperColexBlockMove_neighborhood_card_le h,
    paperColexBlockMove_potential_lt h⟩
end BooleanIsoperimetry
