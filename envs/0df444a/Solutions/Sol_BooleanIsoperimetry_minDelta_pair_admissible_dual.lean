-- Prove2me | solution 1 for BooleanIsoperimetry.minDelta_pair_admissible_dual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:37:52.990209+00:00
-- url     : https://prove2.me/submissions/de1bffc9-e460-4616-9d68-232482fe82e5

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
public import Theorems.Thm_BooleanIsoperimetry_minDelta_pair_admissible_dual_A

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} {A : Finset (Cube N)}
    {T S : Cube N}
    (hdown : IsCoordinateDownFixed A)
    (hT : T ∉ A)
    (hS : S ∈ A)
    (hcard : T.card < S.card)
    (hmin : ∀ T' S' : Cube N, T' ∉ A → S' ∈ A → T'.card < S'.card →
        (S \ T).card + (T \ S).card ≤ (S' \ T').card + (T' \ S').card) :
    ∀ x ∈ S \ T, ∃ y ∈ T \ S, familyUp ((T \ S).erase y) ((S \ T).erase x) Aᶜˢ = Aᶜˢ := by
  intro x hx
  obtain ⟨y, hy, hAeq⟩ :=
    minDelta_pair_admissible_dual_A hdown hT hS hcard hmin x hx
  refine ⟨y, hy, ?_⟩
  have hd : Disjoint ((S \ T).erase x) ((T \ S).erase y) :=
    (disjoint_sdiff_sdiff).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
  have hbridge := familyUp_compls hd A
  rw [hAeq] at hbridge
  exact hbridge.symm
end BooleanIsoperimetry
