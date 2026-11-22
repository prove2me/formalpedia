-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_subset_familyUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:02.818811+00:00
-- url     : https://prove2.me/submissions/e6cfb801-ced3-4dc7-b4ac-74ae0a5af067

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
theorem _root_.solution {N : ℕ} {U V : Cube N} (hd : Disjoint U V)
    {A B : Finset (Cube N)} (hsub : A ⊆ B) :
    familyUp U V A ⊆ familyUp U V B := by
  rw [familyUp_eq_UV_compression A hd, familyUp_eq_UV_compression B hd]
  intro x hx
  rw [UV.mem_compression] at hx ⊢
  rcases hx with ⟨hxA, hcompA⟩ | ⟨hxniA, y, hyA, hcomp⟩
  · exact Or.inl ⟨hsub hxA, hsub hcompA⟩
  · by_cases hxB : x ∈ B
    · refine Or.inl ⟨hxB, ?_⟩
      have H : UV.compress V U x = x := by
        rw [← hcomp, UV.compress_idem]
      rwa [H]
    · exact Or.inr ⟨hxB, y, hsub hyA, hcomp⟩
end BooleanIsoperimetry
