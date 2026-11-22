-- Prove2me | solution 1 for BooleanIsoperimetry.simplicialInitSeg_decomp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:35:07.148176+00:00
-- url     : https://prove2.me/submissions/9a6a35d2-2028-4866-8273-6c02ad3eeb6b

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Combinatorics.Colex
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_BooleanIsoperimetry_KruskalKatona
public import Theorems.Thm_BooleanIsoperimetry_mem_layerInitSeg_iff_rank
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_lt_binomPrefix_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open scoped FinsetFamily
open Finset
open Finset.Colex
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {N r t : ℕ} (ht : t ≤ Nat.choose N r) :
    simplicialInitSeg N (binomPrefix N r + t) =
    (simplicialInitSeg N (binomPrefix N r)) ∪ layerInitSeg N r t := by
  ext x
  simp only [Finset.mem_union, mem_layerInitSeg_iff_rank, simplicialInitSeg, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hrank
    have h_card_le : x.card ≤ r := by
      by_contra! hgt
      have h_rank_ge : binomPrefix N (r + 1) ≤ rank x := by
        have h1 : ¬(x.card < r + 1) := by omega
        have h2 : ¬(rank x < binomPrefix N (r + 1)) :=
          mt (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mp h1
        omega
      have h_rank_lt : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
        have h_eq : binomPrefix N r + Nat.choose N r = binomPrefix N (r + 1) :=
          (binomPrefix_succ N r).symm
        omega
      omega
    rcases lt_or_eq_of_le h_card_le with hlt | heq
    · left
      have h_rank_lt : rank x < binomPrefix N r :=
        (rank_lt_binomPrefix_iff (n := N) (c := r) x).mpr hlt
      exact h_rank_lt
    · right
      exact ⟨heq, by simpa [heq] using binomPrefix_card_le_rank x, hrank⟩
  · rintro (hlt | ⟨heq, _, hrank⟩)
    · omega
    · exact hrank
end BooleanIsoperimetry
