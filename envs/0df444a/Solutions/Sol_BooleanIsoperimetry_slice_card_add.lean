-- Prove2me | solution 1 for BooleanIsoperimetry.slice_card_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:15:20.228341+00:00
-- url     : https://prove2.me/submissions/413c179e-876a-4d54-8d19-53fea4abe955

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n : ℕ} (A : Finset (Cube (n + 1))) :
    (slice0 A).card + (slice1 A).card = A.card := by
  -- Partition `A` by whether the last bit is present.
  have h_partition :
      A = Finset.image (fun x => x.image Fin.castSucc) (slice0 A) ∪
        Finset.image (fun x => insert (Fin.last n) (x.image Fin.castSucc)) (slice1 A) := by
    ext x
    by_cases hx : Fin.last n ∈ x <;>
      simp +decide only [slice0, slice1, Finset.mem_union, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
    · constructor <;> intro h
      · refine Or.inr ⟨ Finset.univ.filter (fun i => Fin.castSucc i ∈ x), ?_, ?_ ⟩ <;>
          simp_all +decide only [Finset.ext_iff, embed1, Finset.mem_insert,
            Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        · convert h using 2; ext i; induction i using Fin.lastCases <;> aesop
        · intro a; induction a using Fin.lastCases <;> aesop
      · unfold embed0 embed1 at h; aesop
    · constructor
      · intro hx'
        refine Or.inl ⟨ Finset.univ.filter fun i => Fin.castSucc i ∈ x, ?_, ?_⟩
        · convert hx' using 1
          ext i; simp only [embed0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ fun ⟨ a, ha₁, ha₂ ⟩ => ha₂ ▸ ha₁,
            fun hi => by cases i using Fin.lastCases <;> aesop ⟩
        · ext i; simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨ fun ⟨ a, ha, ha' ⟩ => ha'.symm ▸ ha,
            fun hi => by cases i using Fin.lastCases <;> aesop ⟩
      · rintro (⟨ a, ha, rfl ⟩ | ⟨ a, ha, rfl ⟩) <;>
          simp_all +decide only [embed0, embed1, Finset.mem_insert, Finset.mem_image,
            Fin.castSucc_ne_last, and_false, exists_false, not_false_eq_true, or_false,
            not_true_eq_false]
  convert congr_arg Finset.card h_partition.symm using 1
  rw [Finset.card_union_of_disjoint] <;> norm_num [Finset.disjoint_right]
  · rw [Finset.card_image_of_injective, Finset.card_image_of_injective] <;>
      norm_num [Function.Injective]
    · intro x y h
      ext i
      replace h := Finset.ext_iff.mp h (Fin.castSucc i)
      simp +decide at h
      tauto
    · exact fun x y h => Finset.image_injective (Fin.castSucc_injective _) h
  · intro a ha x hx H; replace H := Finset.ext_iff.mp H (Fin.last n) ; simp +decide at H
end BooleanIsoperimetry
