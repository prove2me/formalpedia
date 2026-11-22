-- Prove2me | solution 1 for BooleanIsoperimetry.downFixed_familyUp_add_compls_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:23.56867+00:00
-- url     : https://prove2.me/submissions/7e8fda94-7eaf-4e4a-9897-510f67b67a93

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
public import Theorems.Thm_BooleanIsoperimetry_familyUp_compls
public import Theorems.Thm_BooleanIsoperimetry_downFixed_familyUp_erase_eq
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    (hdown : IsCoordinateDownFixed A) (W : Cube N) :
    familyUp ∅ W (Aᶜˢ) = Aᶜˢ := by
  have hd : Disjoint (∅ : Cube N) W := by simp
  have key : (familyUp ∅ W (Aᶜˢ))ᶜˢ = Aᶜˢᶜˢ := by
    rw [familyUp_compls hd, compls_compls, downFixed_familyUp_erase_eq hdown W]
  have := congrArg (fun X => Xᶜˢ) key
  simpa [compls_compls] using this
end BooleanIsoperimetry
