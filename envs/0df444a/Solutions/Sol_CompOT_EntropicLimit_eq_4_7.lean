-- Prove2me | solution 1 for CompOT.EntropicLimit.eq_4_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:57:57.602137+00:00
-- url     : https://prove2.me/submissions/6ad5f74f-c6b8-4a68-a93b-c6db349afafa

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs
set_option autoImplicit false
open CompOT.EntropicLimit

lemma ss_kl_eq {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) (ε : ℝ) (hε : 0 < ε)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    klMat P (gibbs C ε) = entObjective C ε P / ε + ∑ i, ∑ j, gibbs C ε i j := by
  have hterm : ∀ i j, P i j * Real.log (P i j / gibbs C ε i j) - P i j + gibbs C ε i j =
      (C i j * P i j - ε * (Real.negMulLog (P i j) + P i j)) / ε + gibbs C ε i j := by
    intro i j
    have hK : gibbs C ε i j = Real.exp (-C i j / ε) := rfl
    by_cases h0 : P i j = 0
    · rw [h0]; simp [Real.negMulLog]
    · rw [hK, Real.log_div h0 (Real.exp_pos _).ne', Real.log_exp, Real.negMulLog]
      field_simp
      ring
  unfold klMat entObjective CompOT.Assignment.frob entropy
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    IsEntropicOptimal C a b ε P ↔
      (P ∈ CompOT.Assignment.couplings a b ∧
        ∀ Q ∈ CompOT.Assignment.couplings a b, klMat P (gibbs C ε) ≤ klMat Q (gibbs C ε)) := by
  unfold IsEntropicOptimal
  refine and_congr_right fun _ => forall_congr' fun Q => forall_congr' fun _ => ?_
  rw [ss_kl_eq C ε hε P, ss_kl_eq C ε hε Q]
  constructor
  · intro h
    have := div_le_div_of_nonneg_right h hε.le
    linarith
  · intro h
    have h1 : entObjective C ε P / ε ≤ entObjective C ε Q / ε := by linarith
    exact (div_le_div_iff_of_pos_right hε).mp h1
