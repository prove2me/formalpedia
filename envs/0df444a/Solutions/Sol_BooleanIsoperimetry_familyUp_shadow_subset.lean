-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_shadow_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:00.972896+00:00
-- url     : https://prove2.me/submissions/85d45239-54c9-4e1e-a2a2-3418cb53ae90

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
public import Theorems.Thm_BooleanIsoperimetry_familyUp_eq_UV_compression

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)} {U V : Cube N}
    (hd : Disjoint U V) (hUV : IsUVAdmissibleForFamily A U V) :
    shadow (familyUp U V A) ⊆ familyUp U V (shadow A) := by
  rw [familyUp_eq_UV_compression A hd, familyUp_eq_UV_compression (shadow A) hd]
  apply UV.shadow_compression_subset_compression_shadow V U
  intro x hx
  obtain ⟨y, hy, hcomp⟩ := hUV x hx
  refine ⟨y, hy, ?_⟩
  have hde : Disjoint (U.erase y) (V.erase x) := hd.mono (erase_subset _ _) (erase_subset _ _)
  change UV.compression (V.erase x) (U.erase y) A = A
  rw [← familyUp_eq_UV_compression A hde]
  exact hcomp
end BooleanIsoperimetry
