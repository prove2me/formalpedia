-- Prove2me | solution 1 for CJP83.CoverSeparation.integer_lift_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:35:24.141075+00:00
-- url     : https://prove2.me/submissions/f1945fcc-8097-445d-bebb-3bfd09948e55

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
    (S : Finset ι) (f : ι → ℤ) (k : ι) (hk : k ∉ S)
    (z : ℤ) (hz : IsGreatest (liftValues a a₀ S f k) z)
    (zbar : ℝ) (hzbar : IsGreatest (relaxedLiftValues a a₀ S f k) zbar) :
    z ≤ Int.floor zbar := by
  rcases hz.1 with ⟨x, hxS, hx, rfl⟩
  exact Int.le_floor.mpr (hzbar.2 (integer_mem_relaxed a a₀ S f k x hxS hx))
