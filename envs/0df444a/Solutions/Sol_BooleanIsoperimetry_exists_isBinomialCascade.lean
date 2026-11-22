-- Prove2me | solution 1 for BooleanIsoperimetry.exists_isBinomialCascade
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:05.058589+00:00
-- url     : https://prove2.me/submissions/eb2f0869-1207-4390-bc3b-977a23ef82db

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_zero
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_full
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution (n k : ℕ) (hk : k ≤ 2 ^ (n + 1)) :
    ∃ r t, IsBinomialCascade (n + 1) k r t := by
  by_contra! h_contra
  -- Let $r$ be the largest integer such that $binomPrefix (n+1) r \leq k$.
  obtain ⟨r, hr⟩ : ∃ r, r ≤ n + 2 ∧ binomPrefix (n + 1) r ≤ k ∧
      ∀ s, r < s → s ≤ n + 2 → k < binomPrefix (n + 1) s := by
    have hne : (Finset.filter (fun r => binomPrefix (n + 1) r ≤ k) (Finset.Iic (n + 2))).Nonempty :=
      ⟨0, by simp [binomPrefix_zero]⟩
    obtain ⟨hle, hbk⟩ := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    exact ⟨_, Finset.mem_Iic.mp hle, hbk, fun s hs₁ hs₂ => not_le.mp fun hs₃ =>
      hs₁.not_ge (Finset.le_max' _ s (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr hs₂, hs₃⟩))⟩
  refine h_contra r (k - binomPrefix (n + 1) r) ⟨ hr.1, ?_, ?_, ?_ ⟩
  · by_cases hr' : r = n + 2
    · simp_all +decide [binomPrefix_full]
    · have := hr.2.2 (r + 1) (Nat.lt_succ_self r) (Nat.succ_le_of_lt (lt_of_le_of_ne hr.1 hr'))
      simp_all +decide [binomPrefix_succ]
      linarith
  · rw [Nat.add_sub_of_le hr.2.1]
  · by_cases hr_eq : r = n + 2
    · aesop
    · have := hr.2.2 (r + 1) (Nat.lt_succ_self r) (Nat.succ_le_of_lt (lt_of_le_of_ne hr.1 hr_eq))
      simp_all +decide [binomPrefix_succ]
      omega
end BooleanIsoperimetry
