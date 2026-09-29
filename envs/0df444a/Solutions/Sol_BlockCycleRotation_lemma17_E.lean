-- Prove2me | solution 1 for BlockCycleRotation.lemma17_E
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:32:02.026095+00:00
-- url     : https://prove2.me/submissions/8ee5a57b-ed68-45f3-b4b8-1c3e9fb35a3f

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_lemma17_local
import Theorems.Thm_BlockCycleRotation_bulk_empty_of_small
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

/-- **Pairs with small `a` lie in the bulk.**  The contrapositive of
`excluded_pair_large`. -/
theorem bulk_of_small_a {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (h : 2 * d * (a * a) ≤ m) : d * a * (a + a') ≤ m := by
  nlinarith

/-- The cut-off `N = √(m/(2d))` puts every pair with `a ≤ N` in the bulk. -/
theorem bulk_of_le_sqrt {m d a a' : ℕ} (ha' : 1 ≤ a') (haa : a' < a)
    (ha : a ≤ Nat.sqrt (m / (2 * d))) (hd : 0 < d) : d * a * (a + a') ≤ m := by
  refine bulk_of_small_a ha' haa ?_
  have h1 : a * a ≤ m / (2 * d) := by
    have := Nat.sqrt_le' (m / (2 * d))
    calc a * a ≤ Nat.sqrt (m / (2 * d)) * Nat.sqrt (m / (2 * d)) :=
          Nat.mul_le_mul ha ha
      _ ≤ m / (2 * d) := by rw [← pow_two]; exact Nat.sqrt_le' _
  calc 2 * d * (a * a) ≤ 2 * d * (m / (2 * d)) := Nat.mul_le_mul_left _ h1
    _ ≤ m := Nat.mul_div_le m (2 * d)

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

end BlockCycleRotation

open BlockCycleRotation in
/-- **The per-divisor error bound holds.** -/
theorem solution {n : ℕ} (hn : 0 < n) (d : ℕ) (hd : d ∈ n.divisors) :
    |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
          ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
            + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
        - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ Eterm n d:= by
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  unfold Eterm
  by_cases hcase : 2 * d ≤ n / d
  · rw [if_pos hcase]
    have hN : 0 < Nat.sqrt ((n / d) / (2 * d)) := by
      refine Nat.sqrt_pos.2 ?_
      exact (Nat.one_le_div_iff (by omega)).2 hcase
    exact lemma17_local hm hd0 hN (fun a a' ha h1 h2 => bulk_of_le_sqrt h1 h2 ha hd0)
  · rw [if_neg hcase, bulk_empty_of_small (by omega), Finset.sum_empty, zero_sub, abs_neg,
      abs_of_nonneg (mul_nonneg (by positivity) cConst_nonneg)]
