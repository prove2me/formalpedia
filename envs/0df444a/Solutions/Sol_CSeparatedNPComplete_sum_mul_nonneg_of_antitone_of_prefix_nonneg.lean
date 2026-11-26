-- Prove2me | solution 1 for CSeparatedNPComplete.sum_mul_nonneg_of_antitone_of_prefix_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:50:57.8893+00:00
-- url     : https://prove2.me/submissions/8776820b-99e1-49de-bbff-08800bc8378c

module
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Definitions.Def_CSeparatedNPComplete_WeightedSum
public import Theorems.Thm_CSeparatedNPComplete_sum_mul_nonneg_of_antitone_of_partial_sum_nonneg
section
@[expose] public section
namespace CSeparatedNPComplete
open scoped BigOperators
private theorem sum_extendFin {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.range k, extendFin a i) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i := by
  apply Finset.sum_bij (fun i hi => (⟨i, lt_of_lt_of_le (Finset.mem_range.mp hi) hk⟩ : Fin n))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Finset.mem_range.mp hi
  · intro i hi j hj hij
    exact congrArg Fin.val hij
  · intro i hi
    exact ⟨i.val, Finset.mem_range.mpr (Finset.mem_filter.mp hi).2, rfl⟩
  · intro i hi
    simp [extendFin, lt_of_lt_of_le (Finset.mem_range.mp hi) hk]
end CSeparatedNPComplete
end
end

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
open scoped BigOperators
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ}
    (a c : Fin n → ℝ) (hc : Antitone c)
    (ha : ∀ k : ℕ, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i)
    (ht : ∑ i, a i = 0) :
    0 ≤ ∑ i, c i * a i := by
  have hfilter : Finset.univ.filter (fun i : Fin n => i.val < n) = Finset.univ := by
    ext i
    simp
  have h := sum_mul_nonneg_of_antitone_of_partial_sum_nonneg n (extendFin a) (extendFin c)
    (fun i hi => by
      simp only [extendFin, dif_pos hi, dif_pos (show i < n by omega)]
      exact hc (by simp))
    (fun k hk => by rw [sum_extendFin a k hk]; exact ha k)
    (by rw [sum_extendFin a n le_rfl, hfilter]; exact ht)
  have heq : (∑ i ∈ Finset.range n, extendFin c i * extendFin a i) = ∑ i, c i * a i := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp [extendFin]
  rwa [heq] at h
end CSeparatedNPComplete
