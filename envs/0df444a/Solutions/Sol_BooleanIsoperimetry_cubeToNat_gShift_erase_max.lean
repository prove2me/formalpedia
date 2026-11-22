-- Prove2me | solution 1 for BooleanIsoperimetry.cubeToNat_gShift_erase_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:07.554203+00:00
-- url     : https://prove2.me/submissions/06db0355-59cd-4556-bf00-852d486a3220

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_cubeToNat_erase
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} {x : Cube n} (hx : x.Nonempty) (h2 : 2 ≤ x.card) :
    cubeToNat (gShift x) =
      cubeToNat (gShift (x.erase (x.max' hx))) + 2 ^ ((x.max' hx : ℕ)) := by
  by_cases hmax : (x.max' hx) ∈ gShift x
  · rw [cubeToNat_erase]
    focus congr! 1
    · congr! 1
      have hmax' := hmax
      rw [show gShift x = x.erase (x.min' hx) from dif_pos hx, Finset.mem_erase] at hmax'
      have hn : (x.erase (x.max' hx)).Nonempty :=
        ⟨x.min' hx, Finset.mem_erase.mpr ⟨hmax'.1.symm, Finset.min'_mem x hx⟩⟩
      have hm : (x.erase (x.max' hx)).min' hn = x.min' hx := by
        apply le_antisymm
        · exact Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hmax'.1.symm, Finset.min'_mem x hx⟩)
        · exact Finset.min'_le x _ (Finset.mem_of_mem_erase (Finset.min'_mem _ hn))
      simp only [gShift, dif_pos hx, dif_pos hn, hm]
      ext z
      simp only [Finset.mem_erase]
      tauto
    · assumption
  · exfalso
    have h_shift : gShift x = x.erase (x.min' hx) := dif_pos hx
    rw [h_shift, Finset.mem_erase] at hmax
    have h_mem : x.max' hx ∈ x := Finset.max'_mem x hx
    have h_eq : x.max' hx = x.min' hx := by tauto
    have h_card : x.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      have h1 : a = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x a ha) (Finset.min'_le x a ha)
      have h2 : b = x.min' hx := le_antisymm (h_eq ▸ Finset.le_max' x b hb) (Finset.min'_le x b hb)
      rw [h1, h2]
    omega
end BooleanIsoperimetry
