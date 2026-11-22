-- Prove2me | solution 1 for BooleanIsoperimetry.layerInitSeg_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:34:22.266798+00:00
-- url     : https://prove2.me/submissions/0baaaf40-f81d-433b-a226-4d8ee01d5e53

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
public import Theorems.Thm_BooleanIsoperimetry_mem_layerInitSeg_iff
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_card_le_rank
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_le_two_pow
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_exists_rank_eq
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
public import Theorems.Thm_BooleanIsoperimetry_rank_injective
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
    (layerInitSeg N r t).card = t := by
  have hmem : ∀ x : Cube N,
      x ∈ layerInitSeg N r t ↔
        binomPrefix N r ≤ rank x ∧ rank x < binomPrefix N r + t := by
    intro x
    rw [mem_layerInitSeg_iff]
    constructor
    · rintro ⟨hcard, hrank⟩
      exact ⟨by simpa [hcard] using binomPrefix_card_le_rank x, hrank⟩
    · rintro ⟨hlo, hhi⟩
      have hlt_succ : rank x < binomPrefix N (r + 1) := by
        have hs : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
          rw [binomPrefix_succ]
          exact Nat.add_le_add_left ht _
        exact lt_of_lt_of_le hhi hs
      have hcard_lt_succ : x.card < r + 1 :=
        (rank_lt_binomPrefix_iff (n := N) (c := r + 1) x).mp hlt_succ
      have hnot_lt : ¬ x.card < r := by
        intro hxlt
        have hrank_lt : rank x < binomPrefix N r :=
          (rank_lt_binomPrefix_iff (n := N) (c := r) x).mpr hxlt
        exact not_lt_of_ge hlo hrank_lt
      exact ⟨by omega, hhi⟩
  have himage : Finset.image rank (layerInitSeg N r t)
      = Finset.Ico (binomPrefix N r) (binomPrefix N r + t) := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_image.mp hj with ⟨x, hx, rfl⟩
      exact Finset.mem_Ico.mpr ((hmem x).mp hx)
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      have hj_two : j < 2 ^ N := by
        have htop : binomPrefix N r + t ≤ binomPrefix N (r + 1) := by
          rw [binomPrefix_succ]
          exact Nat.add_le_add_left ht _
        exact lt_of_lt_of_le (lt_of_lt_of_le hj'.2 htop) (binomPrefix_le_two_pow N (r + 1))
      obtain ⟨x, hxrank⟩ := exists_rank_eq hj_two
      refine Finset.mem_image.mpr ⟨x, ?_, hxrank⟩
      exact (hmem x).mpr (by simpa [hxrank] using hj')
  rw [← Finset.card_image_of_injective _ rank_injective, himage]
  simp
end BooleanIsoperimetry
