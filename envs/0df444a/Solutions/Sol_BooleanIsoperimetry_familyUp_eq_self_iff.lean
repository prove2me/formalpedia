-- Prove2me | solution 1 for BooleanIsoperimetry.familyUp_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:25:09.184597+00:00
-- url     : https://prove2.me/submissions/5311c672-d653-487e-aae2-06be297047ce

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
theorem _root_.solution {N : ℕ} (W₁ W₂ : Cube N) (A : Finset (Cube N)) :
    familyUp W₁ W₂ A = A ↔
      ∀ R ∈ A, W₁ ⊆ R → Disjoint W₂ R → blockReplace W₁ W₂ R ∈ A := by
  classical
  constructor
  · intro hEq R hR hsub hdisj
    by_contra hnot
    have hguard : W₁ ⊆ R ∧ Disjoint W₂ R ∧ blockReplace W₁ W₂ R ∉ A := ⟨hsub, hdisj, hnot⟩
    have hmap : familyUpMap W₁ W₂ A R = blockReplace W₁ W₂ R := by
      unfold familyUpMap; rw [if_pos hguard]
    have hmem : blockReplace W₁ W₂ R ∈ familyUp W₁ W₂ A := by
      rw [familyUp, Finset.mem_image]; exact ⟨R, hR, hmap⟩
    rw [hEq] at hmem; exact hnot hmem
  · intro hClosed
    have hmap : ∀ R ∈ A, familyUpMap W₁ W₂ A R = R := by
      intro R hR
      unfold familyUpMap
      by_cases hguard : W₁ ⊆ R ∧ Disjoint W₂ R ∧ blockReplace W₁ W₂ R ∉ A
      · exact absurd (hClosed R hR hguard.1 hguard.2.1) hguard.2.2
      · rw [if_neg hguard]
    unfold familyUp
    rw [Finset.image_congr (g := id) (fun R hR => hmap R hR), Finset.image_id]
end BooleanIsoperimetry
