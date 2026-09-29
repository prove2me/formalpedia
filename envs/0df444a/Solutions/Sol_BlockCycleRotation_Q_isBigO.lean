-- Prove2me | solution 1 for BlockCycleRotation.Q_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:53:08.512505+00:00
-- url     : https://prove2.me/submissions/1ce11c20-0d21-4f5a-b229-078d31f92d5d

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Theorems.Thm_BlockCycleRotation_Q_symmetrise
import Theorems.Thm_BlockCycleRotation_sum_diag_isBigO
import Theorems.Thm_BlockCycleRotation_error_isBigO
import Theorems.Thm_BlockCycleRotation_lemma17_isBigO
import Theorems.Thm_BlockCycleRotation_Qgt_sub_G1_le
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

end BlockCycleRotation

open BlockCycleRotation in
/-- **`Q(n) = C·n²·∑_{d∣n} 1/d² + O(n^{3/2+ε})`.** -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 0 < n →
      |((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
        ≤ K * (n : ℝ) ^ (3 / 2 + ε):= by
  classical
  obtain ⟨C1, hC1, hErr⟩ := error_isBigO hε
  obtain ⟨C2, hC2, hDiag⟩ := sum_diag_isBigO hε
  obtain ⟨C3, hC3, hG1⟩ := lemma17_isBigO hε
  refine ⟨5 * C1 + C2 + C3, by positivity, fun n hn => ?_⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsym : ((Qquad n : ℤ) : ℝ)
      = ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ)
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ) := by
    have h1 : (Qquad n : ℤ) = ((∑ q ∈ quadruplesQ n, q.2.1 : ℕ) : ℤ) := by
      unfold Qquad; push_cast; rfl
    rw [h1, Q_symmetrise n]
    push_cast
    ring
  have hdiagnn : (0 : ℝ)
      ≤ ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ) := by positivity
  have hexp : (n : ℝ) ^ (1 + ε) ≤ (n : ℝ) ^ (3 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
  have h1 := Qgt_sub_G1_le hn
  have h2 := hErr n hn
  have h3 := hDiag n hn
  have h4 := hG1 n hn
  have hsplit : ((Qquad n : ℤ) : ℝ) - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2
      = (((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n)
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ)
        + (G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2) := by
    rw [hsym]; ring
  rw [hsplit]
  have hA := abs_add_le
    ((((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n)
      + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ))
    (G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2)
  have hB := abs_add_le
    ((((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1) : ℕ) : ℝ) - G1 n))
    (((∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 : ℕ) : ℝ))
  rw [abs_of_nonneg hdiagnn] at hB
  have hErrle : 5 * Err n ≤ 5 * (C1 * (n : ℝ) ^ (3 / 2 + ε)) := by
    have : Err n ≤ C1 * (n : ℝ) ^ (3 / 2 + ε) := h2
    linarith
  nlinarith [hA, hB, h1, h3, h4, hErrle, hexp, hC2]
