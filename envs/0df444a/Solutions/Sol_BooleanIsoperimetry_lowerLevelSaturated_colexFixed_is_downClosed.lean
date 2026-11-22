-- Prove2me | solution 1 for BooleanIsoperimetry.lowerLevelSaturated_colexFixed_is_downClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:14.757923+00:00
-- url     : https://prove2.me/submissions/6e6c601d-64f0-4e93-89c6-fafaab617772

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_SimplicialCompression
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_simplicialLe_antisymm
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open Finset
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N : ℕ} (A : Finset (Cube N))
    (hLower : IsLowerLevelSaturated A)
    (hColex : IsColexShiftFixed A) :
    ∀ x y, simplicialLe x y → y ∈ A → x ∈ A := by
  intro x y hxy hyA
  unfold simplicialLe at hxy
  rcases hxy with hcard | ⟨hcard, hnat⟩
  · exact hLower hcard hyA
  · by_cases hxA : x ∈ A
    · exact hxA
    · have hlt : simplicialLt x y := by
        refine ⟨?_, ?_⟩
        · unfold simplicialLe
          exact Or.inr ⟨hcard, hnat⟩
        · intro hyx
          exact hxA ((simplicialLe_antisymm x y
            (by unfold simplicialLe; exact Or.inr ⟨hcard, hnat⟩) hyx).symm ▸ hyA)
      have hshift : IsColexShift A (insert x (A.erase y)) := by
        refine ⟨?_, ⟨y, x, hyA, hxA, hcard.symm, hlt, rfl⟩⟩
        rw [card_insert_of_notMem]
        · rw [card_erase_of_mem hyA]
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨y, hyA⟩
          omega
        · simp [hxA]
      exact (hColex (insert x (A.erase y)) hshift).elim
end BooleanIsoperimetry
