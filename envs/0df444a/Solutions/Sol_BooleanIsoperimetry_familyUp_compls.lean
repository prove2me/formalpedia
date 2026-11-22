-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_compls
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:36:47.943801+00:00
-- url     : https://prove2.me/submissions/0492f00c-ab39-4729-8e69-c24c16e2062f

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
public import Theorems.Thm_BooleanIsoperimetry_familyUpMap_compl

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {U V : Cube N} (hd : Disjoint U V) (A : Finset (Cube N)) :
    (familyUp U V A)ᶜˢ = familyUp V U (Aᶜˢ) := by
  have hL : (familyUp U V A)ᶜˢ = A.image (fun S => (familyUpMap U V A S)ᶜ) := by
    rw [familyUp, ← Finset.image_compl, Finset.image_image]; rfl
  have hR : familyUp V U (Aᶜˢ) = A.image (fun S => familyUpMap V U (Aᶜˢ) Sᶜ) := by
    rw [familyUp, ← Finset.image_compl, Finset.image_image]; rfl
  rw [hL, hR]
  exact Finset.image_congr (fun S _hS => familyUpMap_compl hd A S)
end BooleanIsoperimetry
