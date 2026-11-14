-- Prove2me | solution 1 for ConsistentSubmodular.Checkpoints.exists_subset_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:09.402776+00:00
-- url     : https://prove2.me/submissions/855822f0-bf16-42b3-975f-0efda0e5c7ae

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Checkpoints_sum_deletion_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- Some element of a nonempty set `A` costs at most `f(A)/|A|` when deleted. -/
theorem exists_cheap_deletion (f : Objective n) {A : Finset (Fin n)} (hA : A.Nonempty) :
    ∃ e ∈ A, (A.card : ℝ) * (f.value A - f.value (A.erase e)) ≤ f.value A := by
  have hsum := sum_deletion_le f A
  have h0 := f.nonnegative ∅
  have hle : ∑ e ∈ A, (A.card : ℝ) * (f.value A - f.value (A.erase e)) ≤
      ∑ _e ∈ A, f.value A := by
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    have hc : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    nlinarith
  exact Finset.exists_le_of_sum_le hA hle

end ConsistentSubmodular.Checkpoints

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Checkpoints
variable {n : ℕ}

theorem solution (f : Objective n) :
    ∀ (m : ℕ) (A : Finset (Fin n)), A.card = m → ∀ r ≤ m,
      ∃ T ⊆ A, T.card = r ∧ (r : ℝ) * f.value A ≤ m * f.value T := by
  intro m
  induction m with
  | zero =>
    intro A hA r hr
    refine ⟨A, Finset.Subset.refl A, by omega, ?_⟩
    have : r = 0 := by omega
    subst this
    simp
  | succ m ih =>
    intro A hA r hr
    rcases Nat.lt_or_ge r (m + 1) with hr' | hr'
    · have hne : A.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨e, he, hcheap⟩ := exists_cheap_deletion f hne
      have hcard : (A.erase e).card = m := by rw [Finset.card_erase_of_mem he, hA]; rfl
      obtain ⟨T, hT, hTcard, hTval⟩ := ih (A.erase e) hcard r (by omega)
      refine ⟨T, hT.trans (Finset.erase_subset e A), hTcard, ?_⟩
      rw [hA] at hcheap
      push_cast at hcheap ⊢
      have hfT := f.nonnegative T
      have hfA := f.nonnegative A
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        have : r = 0 := by omega
        subst this
        simp only [CharP.cast_eq_zero, zero_mul, zero_add, one_mul]
        exact hfT
      · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hrR : (r : ℝ) ≤ m := by exact_mod_cast (show r ≤ m by omega)
        have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        -- `m f(A) ≤ (m+1) f(A \ e)` and `r f(A \ e) ≤ m f(T)`.
        have h1 : (m : ℝ) * f.value A ≤ (m + 1) * f.value (A.erase e) := by linarith
        have h2 : (m : ℝ) * ((r : ℝ) * f.value A) ≤ (m : ℝ) * ((m + 1) * f.value T) := by
          calc (m : ℝ) * ((r : ℝ) * f.value A) = r * (m * f.value A) := by ring
            _ ≤ r * ((m + 1) * f.value (A.erase e)) := mul_le_mul_of_nonneg_left h1 hr0
            _ = (m + 1) * (r * f.value (A.erase e)) := by ring
            _ ≤ (m + 1) * (m * f.value T) := by
                apply mul_le_mul_of_nonneg_left hTval
                positivity
            _ = (m : ℝ) * ((m + 1) * f.value T) := by ring
        exact le_of_mul_le_mul_left h2 hmR
    · have : r = m + 1 := by omega
      subst this
      exact ⟨A, Finset.Subset.refl A, hA, le_refl _⟩

end
