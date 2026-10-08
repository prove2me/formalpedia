-- Prove2me | solution 1 for CJP83.CoverSeparation.relaxed_lifting_valid
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:37:57.50558+00:00
-- url     : https://prove2.me/submissions/73947ee0-2c07-4c40-9c72-bc50d55b5205

import Mathlib
import Definitions.Def_CJP83_CoverSeparation_KnapsackRow

open CJP83.CoverSeparation
open scoped BigOperators

private lemma sum_binary_mul {ι : Type*} [DecidableEq ι] (g : ι → ℝ)
    (S x : Finset ι) (hx : x ⊆ S) :
    (∑ j ∈ S, g j * binaryValue x j) = ∑ j ∈ x, g j := by
  calc
    _ = ∑ j ∈ x, g j * binaryValue x j := by
      symm
      apply Finset.sum_subset hx
      intro j hjS hjx
      simp [binaryValue, hjx]
    _ = _ := by apply Finset.sum_congr rfl; intro j hj; simp [binaryValue, hj]

private lemma integer_mem_relaxed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (S : Finset ι) (f : ι → ℤ) (k : ι)
    (x : Finset ι) (hxS : x ⊆ S) (hx : (∑ j ∈ x, a j) ≤ a₀ - a k) :
    (((∑ j ∈ x, f j) : ℤ) : ℝ) ∈ relaxedLiftValues a a₀ S f k := by
  refine ⟨binaryValue x, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hjx : j ∉ x := fun h => hj (hxS h)
    simp [binaryValue, hjx]
  · intro j hj
    simp only [binaryValue]
    split <;> constructor <;> norm_num
  · rw [sum_binary_mul _ S x hxS]
    exact_mod_cast hx
  · rw [sum_binary_mul _ S x hxS]
    norm_cast

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℚ) (a₀ : ℚ) (hpos : ∀ j, 0 < a j)
    (S : Finset ι) (f : ι → ℤ) (f₀ : ℤ) (k : ι) (hk : k ∉ S)
    (hvalid : IsValidOn a a₀ S f f₀)
    (zbar : ℝ) (hzbar : IsGreatest (relaxedLiftValues a a₀ S f k) zbar) :
    IsValidOn a a₀ (insert k S) (Function.update f k (f₀ - Int.floor zbar)) f₀ := by
  intro x hxS hx
  by_cases hkx : k ∈ x
  · have herase : x.erase k ⊆ S := by
      intro j hj
      have hjx := (Finset.mem_erase.mp hj).2
      have hjk := (Finset.mem_erase.mp hj).1
      exact (Finset.mem_insert.mp (hxS hjx)).resolve_left hjk
    have hrow : (∑ j ∈ x.erase k, a j) ≤ a₀ - a k := by
      rw [Finset.sum_erase_eq_sub hkx]
      exact sub_le_sub_right hx _
    have hsum : (∑ j ∈ x.erase k, f j) ≤ Int.floor zbar :=
      Int.le_floor.mpr (hzbar.2 (integer_mem_relaxed a a₀ S f k (x.erase k) herase hrow))
    have heq : (∑ j ∈ x.erase k, Function.update f k (f₀ - Int.floor zbar) j) =
        ∑ j ∈ x.erase k, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    have hsplit := Finset.sum_erase_add x (Function.update f k (f₀ - Int.floor zbar)) hkx
    rw [heq, Function.update_self] at hsplit
    omega
  · have hxS' : x ⊆ S := by
      intro j hj
      exact (Finset.mem_insert.mp (hxS hj)).resolve_left (fun heq => hkx (heq ▸ hj))
    have heq : (∑ j ∈ x, Function.update f k (f₀ - Int.floor zbar) j) = ∑ j ∈ x, f j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≠ k := fun heq => hkx (heq ▸ hj)
      exact Function.update_of_ne hjk _ _
    rw [heq]
    exact hvalid x hxS' hx
