-- Prove2me | solution 1 for BlockCycleRotation.cConst_le_bulk_add
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:28:58.149593+00:00
-- url     : https://prove2.me/submissions/7f2e7fec-fff2-4c62-a7c6-8ca67643bb56

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cConst_le_partial_add
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **The truncation bound.**  Restricting the series for `C` to the bulk pairs
loses at most `3/(2N)`, provided every pair with `a ≤ N` lies in the bulk. -/
theorem solution {m d N : ℕ} (hN : 0 < N)
    (hbulk : ∀ a a', a ≤ N → 1 ≤ a' → a' < a → d * a * (a + a') ≤ m) :
    cConst ≤ (∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a,
        if d * a * (a + a') ≤ m then cTerm (a, a') else 0) + 3 / (2 * (N : ℝ)):= by
  refine le_trans (cConst_le_partial_add hN) ?_
  have heq : ∀ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, cTerm (a, a')
      = ∑ a' ∈ Finset.range a, if d * a * (a + a') ≤ m then cTerm (a, a') else 0 := by
    intro a ha
    simp only [Finset.mem_range, Nat.lt_succ_iff] at ha
    refine Finset.sum_congr rfl fun a' ha' => ?_
    simp only [Finset.mem_range] at ha'
    rcases Nat.eq_zero_or_pos a' with h0 | h0
    · subst h0
      have hz : cTerm (a, 0) = 0 := by
        unfold cTerm
        rw [if_neg]
        rintro ⟨h1, -, -⟩
        omega
      simp [hz]
    · rw [if_pos (hbulk a a' ha h0 ha')]
  rw [Finset.sum_congr rfl heq]
