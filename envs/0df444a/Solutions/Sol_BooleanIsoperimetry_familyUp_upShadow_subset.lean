-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_upShadow_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:40.102954+00:00
-- url     : https://prove2.me/submissions/c55c10de-7849-4cdc-9e33-29e440df4466

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
public import Theorems.Thm_BooleanIsoperimetry_familyUp_shadow_subset

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
    upShadow (familyUp U V A) ⊆ familyUp U V (upShadow A) := by
  have h_shad := familyUp_shadow_subset hd.symm hUV'
  have h_shad_comp := compls_subset_compls.mpr h_shad
  have H1 : compls (shadow (familyUp V U (compls A))) = upShadow (familyUp U V A) := by
    rw [← familyUp_compls hd, Finset.shadow_compls, compls_compls]
  have H2 : compls (familyUp V U (shadow (compls A))) = familyUp U V (upShadow A) := by
    have h_comp_sh : shadow (compls A) = compls (upShadow A) := Finset.shadow_compls
    rw [h_comp_sh, familyUp_compls hd.symm, compls_compls]
  rwa [H1, H2] at h_shad_comp
end BooleanIsoperimetry
