-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_upperShadow_card_le_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:43:22.716773+00:00
-- url     : https://prove2.me/submissions/ae5c4308-008c-41e0-89b0-60c5e9915b26

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
public import Theorems.Thm_BooleanIsoperimetry_familyUp_shadow_card_le_of_admissible
public import Theorems.Thm_BooleanIsoperimetry_familyUp_compls

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV' : IsUVAdmissibleForFamily (Aᶜˢ) V U) :
    ((familyUp U V A)ᶜˢ).shadow.card ≤ (Aᶜˢ).shadow.card := by
  rw [familyUp_compls hd]
  exact familyUp_shadow_card_le_of_admissible hd.symm hUV'
end BooleanIsoperimetry
