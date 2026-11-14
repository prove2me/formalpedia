-- Prove2me | solution 1 for ConsistentSubmodular.Objective.exists_thinned_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:31:30.557294+00:00
-- url     : https://prove2.me/submissions/31afa16a-9ca5-45ae-90c8-bf36765e6d36

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Objective_sum_removal_marginals_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Objective

variable {n : ℕ} (f : Objective n)

theorem exists_efficient_deletion {A : Finset (Fin n)} (hA : A.Nonempty) :
    ∃ e ∈ A, ((A.card : ℝ) - 1) * f.value A ≤
      (A.card : ℝ) * f.value (A.erase e) := by
  classical
  have hcard : (0 : ℝ) < A.card := Nat.cast_pos.mpr hA.card_pos
  have hsum : (∑ e ∈ A, (f.value A - f.value (A.erase e))) ≤
      ∑ _e ∈ A, f.value A / A.card := by
    have h := f.sum_removal_marginals_le A
    have h0 := f.nonnegative ∅
    have hc : (A.card : ℝ) * (f.value A / A.card) = f.value A := by
      field_simp
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    linarith
  obtain ⟨e, he, hmarg⟩ := Finset.exists_le_of_sum_le hA hsum
  refine ⟨e, he, ?_⟩
  have hscaled := (le_div_iff₀ hcard).mp hmarg
  nlinarith

end ConsistentSubmodular.Objective

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A : Finset (Fin n)) (r : ℕ) (hr : r ≤ A.card) :
    ∃ B ⊆ A, B.card = r ∧ (r : ℝ) * f.value A ≤ (A.card : ℝ) * f.value B := by
  classical
  induction hs : A.card using Nat.strong_induction_on generalizing A with
  | h s ih =>
    rw [← hs]
    by_cases hr0 : r = 0
    · subst r
      exact ⟨∅, Finset.empty_subset A, by simp,
        by simpa using mul_nonneg (Nat.cast_nonneg A.card) (f.nonnegative ∅)⟩
    by_cases hrs : r = A.card
    · exact ⟨A, Finset.Subset.refl A, hrs.symm, by rw [hrs]⟩
    have hrslt : r < A.card := lt_of_le_of_ne hr hrs
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he, hdel⟩ := f.exists_efficient_deletion hA
    have hcard : (A.erase e).card + 1 = A.card := Finset.card_erase_add_one he
    have hsmall : (A.erase e).card < s := by omega
    have hrsmall : r ≤ (A.erase e).card := by omega
    obtain ⟨B, hBA, hBr, hBval⟩ := ih (A.erase e).card hsmall
      (A.erase e) hrsmall rfl
    refine ⟨B, hBA.trans (Finset.erase_subset e A), hBr, ?_⟩
    have hc : ((A.erase e).card : ℝ) + 1 = (A.card : ℝ) := by exact_mod_cast hcard
    have hcpos : (0 : ℝ) < (A.erase e).card := by exact_mod_cast (show 0 < (A.erase e).card by omega)
    have hdel' := mul_le_mul_of_nonneg_left hdel (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    have hBval' := mul_le_mul_of_nonneg_left hBval (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)
    have hcombined : ((A.erase e).card : ℝ) * ((r : ℝ) * f.value A) ≤
        ((A.erase e).card : ℝ) * ((A.card : ℝ) * f.value B) := calc
      _ = (r : ℝ) * (((A.card : ℝ) - 1) * f.value A) := by rw [← hc]; ring
      _ ≤ (r : ℝ) * ((A.card : ℝ) * f.value (A.erase e)) := hdel'
      _ = (A.card : ℝ) * ((r : ℝ) * f.value (A.erase e)) := by ring
      _ ≤ (A.card : ℝ) * ((A.erase e).card * f.value B) := hBval'
      _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hcpos).mp hcombined

end
