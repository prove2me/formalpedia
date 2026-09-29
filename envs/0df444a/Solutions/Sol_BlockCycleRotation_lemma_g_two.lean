-- Prove2me | solution 1 for BlockCycleRotation.lemma_g_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:51:45.766812+00:00
-- url     : https://prove2.me/submissions/0165fb14-c282-4298-ad53-cea0994a6bdc

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_error_isBigO
import Theorems.Thm_BlockCycleRotation_abs_G2term_le
import Theorems.Thm_BlockCycleRotation_aggregate_le
import Mathlib

open Finset Real

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
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_coprimePairs {m a a' : ℕ} :
    (a, a') ∈ coprimePairs m ↔ (a ≤ m ∧ a' ≤ m) ∧ 1 ≤ a' ∧ a' < a ∧ Nat.gcd a a' = 1 := by
  simp [coprimePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem abs_G2sum_le {n : ℕ} (hn : 0 < n) : |G2sum n| ≤ Err n := by
  refine aggregate_le hn (fun m d a a' => G2term m d a a') fun d hd p hp => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm0 : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  obtain ⟨a, a'⟩ := p
  rw [Finset.mem_filter] at hp
  obtain ⟨hpc, hpb⟩ := hp
  have hpb' : d * a * (a + a') ≤ n / d := hpb
  obtain ⟨-, ha1, haa, hgcd⟩ := mem_coprimePairs.1 hpc
  have ha : 0 < a := by omega
  have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hmR : (1 : ℝ) ≤ ((n / d : ℕ) : ℝ) := by exact_mod_cast hm0
  have hlog : (0 : ℝ) ≤ Real.log ((n / d : ℕ) : ℝ) := Real.log_nonneg hmR
  have hb := abs_G2term_le hm0 hd0 ha1 haa hpb'
  -- `|A| + |B|·Y ≤ d·a + 2m/a`
  have hAabs : |aCoeff (n / d) d a| = aCoeff (n / d) d a :=
    abs_of_nonneg (by unfold aCoeff; positivity)
  have hBabs : |bCoeff a a'| = (a' : ℝ) / (a : ℝ) := by
    unfold bCoeff
    rw [abs_div, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ (a' : ℝ)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (a : ℝ))]
  have hsR : (0 : ℝ) < (a : ℝ) + (a' : ℝ) := by
    have h1 : (0 : ℝ) ≤ (a' : ℝ) := by positivity
    have h2 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    linarith
  have hBY : |bCoeff a a'| * yCut (n / d) a a' ≤ ((n / d : ℕ) : ℝ) / (a : ℝ) := by
    rw [hBabs, yCut, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have hma : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) * (a : ℝ) * (a : ℝ) := by positivity
    nlinarith [hma, Nat.cast_nonneg (α := ℝ) a']
  have hW : |aCoeff (n / d) d a| + |bCoeff a a'| * yCut (n / d) a a'
      ≤ ((d * a : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by
    rw [hAabs]
    unfold aCoeff
    have : ((n / d : ℕ) : ℝ) / (a : ℝ) + ((n / d : ℕ) : ℝ) / (a : ℝ)
        = 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by ring
    linarith [hBY]
  have hWnn : (0 : ℝ) ≤ ((d * a : ℕ) : ℝ) + 2 * ((n / d : ℕ) : ℝ) / (a : ℝ) := by positivity
  nlinarith [hb, hW, hWnn, hlog]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Lemma 18.**  `G₂(n) = O(n^{3/2+ε})`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |G2sum n| ≤ C * (n : ℝ) ^ (3 / 2 + ε):= by
  obtain ⟨C, hC, hErr⟩ := error_isBigO hε
  exact ⟨C, hC, fun n hn => le_trans (abs_G2sum_le hn) (hErr n hn)⟩
