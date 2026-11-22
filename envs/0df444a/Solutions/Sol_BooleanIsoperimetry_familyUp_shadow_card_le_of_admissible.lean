-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_shadow_card_le_of_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:02.079824+00:00
-- url     : https://prove2.me/submissions/68149c8b-e17a-4112-884e-8526fd0ecfc1

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
    (familyUp U V A).shadow.card ≤ A.shadow.card := by
  rw [familyUp_eq_UV_compression A hd]
  apply UV.card_shadow_compression_le V U
  intro x hx
  obtain ⟨y, hy, hcomp⟩ := hUV x hx
  refine ⟨y, hy, ?_⟩
  have hde : Disjoint (U.erase y) (V.erase x) :=
    hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  change UV.compression (V.erase x) (U.erase y) A = A
  rw [← familyUp_eq_UV_compression A hde]
  exact hcomp
end BooleanIsoperimetry
