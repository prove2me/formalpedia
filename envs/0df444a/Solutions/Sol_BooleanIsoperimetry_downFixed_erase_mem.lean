-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_erase_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:29.105101+00:00
-- url     : https://prove2.me/submissions/4f29db7e-7324-48cd-8386-0a96c5c804b3

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
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) {x : Cube N} (hx : x ∈ A) {i : Fin N} (hi : i ∈ x) :
    x.erase i ∈ A := by
  have hfix := (hdown i).2 x
  have hmem : x ∈ A := hx
  rw [hfix] at hmem
  rcases hmem with ⟨_, hcase⟩ | ⟨hi', _, _⟩
  · rcases hcase with hni | herase
    · exact absurd hi hni
    · exact herase
  · exact absurd hi hi'
end BooleanIsoperimetry
