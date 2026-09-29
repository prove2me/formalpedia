-- Prove2me | solution 1 for BlockCycleRotation.bulk_double_le_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:29:39.388726+00:00
-- url     : https://prove2.me/submissions/5b3c97c1-e8e6-4dd1-880e-8d043b74ab8e

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_double_sum_eq_pairs
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

end BlockCycleRotation

open BlockCycleRotation in
/-- **The reconciliation.**  The double sum over `a ≤ N` is at most the sum over
the bulk pairs. -/
theorem solution {m d N : ℕ} (hd : 0 < d) :
    ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
        (if d * a * (a + a') ≤ m then cTerm (a, a') else 0)
      ≤ ∑ p ∈ (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m), cTerm p:= by
  classical
  rw [double_sum_eq_pairs (fun a a' => if d * a * (a + a') ≤ m then cTerm (a, a') else 0)]
  set P := ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.2 < p.1) with hP
  set B := (coprimePairs m).filter (fun p => d * p.1 * (p.1 + p.2) ≤ m) with hB
  -- every nonzero term of the left sum sits at a bulk pair
  have hzero : ∀ p ∈ P, p ∉ B →
      (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0) = 0 := by
    rintro ⟨a, a'⟩ hp hnb
    by_cases hbulk : d * a * (a + a') ≤ m
    · simp only [hbulk, if_true]
      -- the pair must fail admissibility, else it would lie in `B`
      unfold cTerm
      rw [if_neg]
      rintro ⟨h1, h2, h3⟩
      have h1' : 1 ≤ a' := h1
      have h2' : a' < a := h2
      have h3' : Nat.gcd a a' = 1 := h3
      have hd1 : 1 ≤ d := hd
      have ham : a ≤ m := by
        have ha1 : 1 ≤ a := by omega
        have haa : 1 ≤ a + a' := by omega
        have hstep : a ≤ d * a * (a + a') := by
          calc a = 1 * a * 1 := by ring
            _ ≤ d * a * (a + a') := Nat.mul_le_mul (Nat.mul_le_mul hd1 (le_refl a)) haa
        omega
      have ha'm : a' ≤ m := by omega
      refine hnb ?_
      rw [hB]
      simp only [Finset.mem_filter]
      exact ⟨mem_coprimePairs.2 ⟨⟨ham, ha'm⟩, h1', h2', h3'⟩, hbulk⟩
    · simp [hbulk]
  calc ∑ p ∈ P, (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0)
      = ∑ p ∈ P.filter (fun p => p ∈ B),
          (if d * p.1 * (p.1 + p.2) ≤ m then cTerm (p.1, p.2) else 0) := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
        intro x hx hnx
        simp only [Finset.mem_filter, not_and] at hnx
        exact hzero x hx (hnx hx)
    _ ≤ ∑ p ∈ P.filter (fun p => p ∈ B), cTerm p := by
        refine Finset.sum_le_sum fun p _ => ?_
        split
        · exact le_refl _
        · exact cTerm_nonneg p
    _ ≤ ∑ p ∈ B, cTerm p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => cTerm_nonneg p)
        intro x hx
        simp only [Finset.mem_filter] at hx
        exact hx.2
