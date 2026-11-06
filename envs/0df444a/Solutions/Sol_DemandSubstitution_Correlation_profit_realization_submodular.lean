-- Prove2me | solution 1 for DemandSubstitution.Correlation.profit_realization_submodular
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T22:16:49.674159+00:00
-- url     : https://prove2.me/submissions/890befd9-3b81-4de3-9b81-30d6d3510356

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_DemandSubstitution_Correlation_Setting
import Theorems.Thm_DemandSubstitution_Correlation_min_h_submodular

open DemandSubstitution.Correlation Supermodularity.Monotonicity

private lemma firm_eq {n : ℕ} (M : Model n) (Q x : Fin n → ℝ) (k : Fin n) :
    firmProfitAt M Q x k = (M.u k + M.o k) * min (Ds M Q x k) (Q k) - M.o k * Q k := by
  unfold firmProfitAt
  rcases le_total (Ds M Q x k) (Q k) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

private lemma firm_sm {n : ℕ} (M : Model n) (Q : Fin n → ℝ) (hQ : ∀ k, 0 ≤ Q k) (k : Fin n) :
    SupermodularOn (fun x => -firmProfitAt M Q x k) Set.univ := by
  intro x hx y hy
  have h := min_h_submodular M Q hQ k hx hy
  simp only [firm_eq] at *
  have hpos : 0 ≤ M.u k + M.o k := by
    unfold Model.u Model.o; linarith [M.c_lt_r k, M.s_lt_c k]
  have := mul_le_mul_of_nonneg_left h hpos
  nlinarith

theorem solution {n : ℕ} (M : Model n) (Q : Fin n → ℝ)
    (hQ : ∀ k, 0 ≤ Q k) :
    (∀ x, profitAt M Q x = ∑ i, ((M.u i + M.o i) * min (Ds M Q x i) (Q i) - M.o i * Q i)) ∧
      SupermodularOn (fun x => -profitAt M Q x) Set.univ ∧
      ∀ k, SupermodularOn (fun x => -firmProfitAt M Q x k) Set.univ := by
  refine ⟨fun x => ?_, ?_, firm_sm M Q hQ⟩
  · unfold profitAt
    exact Finset.sum_congr rfl fun k _ => firm_eq M Q x k
  · intro x hx y hy
    have h : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        -firmProfitAt M Q x k + -firmProfitAt M Q y k ≤
          -firmProfitAt M Q (x ⊔ y) k + -firmProfitAt M Q (x ⊓ y) k :=
      fun k _ => firm_sm M Q hQ k hx hy
    have := Finset.sum_le_sum h
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib] at this
    simp only [profitAt]
    linarith
