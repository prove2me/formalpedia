-- Prove2me | solution 1 for BlockCycleRotation.lemma17_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:33:44.031402+00:00
-- url     : https://prove2.me/submissions/041eea82-da4e-4efa-a944-865515d083de

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_lemma17_final
import Theorems.Thm_BlockCycleRotation_Eterm_le
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

theorem cTerm_nonneg (p : ℕ × ℕ) : 0 ≤ cTerm p := by
  unfold cTerm
  split
  · positivity
  · exact le_refl 0

theorem cConst_nonneg : 0 ≤ cConst :=
  tsum_nonneg fun p => cTerm_nonneg p

/-- **The errors sum to at most `d(n)` times their maximum.** -/
theorem sum_divisors_le {n : ℕ} (g : ℕ → ℝ) (K : ℝ)
    (hg : ∀ d ∈ n.divisors, g d ≤ K) :
    ∑ d ∈ n.divisors, g d ≤ (n.divisors.card : ℝ) * K := by
  calc ∑ d ∈ n.divisors, g d ≤ ∑ _d ∈ n.divisors, K := Finset.sum_le_sum hg
    _ = (n.divisors.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `x^{3/2} = x·√x`. -/
theorem rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add' hx (by norm_num), Real.rpow_one]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Lemma 17 in the paper's form.**  The total error is `O(n^{3/2+ε})`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε):= by
  obtain ⟨C0, hC0, hCd⟩ := exists_card_divisors_le hε
  refine ⟨(8 + 2 * cConst) * C0, mul_pos (by linarith [cConst_nonneg]) hC0, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hCnn : (0 : ℝ) ≤ cConst := cConst_nonneg
  have h32 : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) :=
    (rpow_three_halves (by positivity)).symm
  refine (lemma17_final hn).trans ?_
  refine (sum_divisors_le _ _ (fun d hd => Eterm_le hn hd)).trans ?_
  have hd := hCd n hn.ne'
  have hstep : (n.divisors.card : ℝ) * ((8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n))
      ≤ (C0 * (n : ℝ) ^ ε) * ((8 + 2 * cConst) * ((n : ℝ) * Real.sqrt n)) := by
    refine mul_le_mul_of_nonneg_right hd ?_
    have hs0 : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
    exact mul_nonneg (by linarith) (mul_nonneg (by linarith) hs0)
  refine hstep.trans ?_
  rw [h32, Real.rpow_add hnpos]
  exact le_of_eq (by ring)
