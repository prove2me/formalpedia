-- Prove2me | solution 1 for BankIntegration.Reversal.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:19:15.453204+00:00
-- url     : https://prove2.me/submissions/02080575-4e9f-4efd-9c18-16d702f90593

import Mathlib
import Definitions.Def_BankIntegration_Reversal_Model
import Theorems.Thm_BankIntegration_Reversal_lemma_6a

open BankIntegration.Reversal in
theorem solution (lam a1 a2 b1 b2 : ℝ) (n : ℕ) (hS : Standing lam a1 a2 b1 b2 n) :
    (∃! L : Fin (2 * n) → ℝ, IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) L) ∧
    (∀ L : Fin (2 * n) → ℝ, IsCournotEq lam 0 (a1 + a2) (b1 + b2) (2 * n) L →
      (∀ i, ∑ k, L k = 2 * (n : ℝ) * L i) ∧
      depositRate (a1 + a2) (∑ k, L k) =
        lam * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) *
          (xiStar a1 a2 b1 b2 / (1 + xiStar a1 a2 b1 b2)) ∧
      loanRate lam (b1 + b2) (∑ k, L k) =
        lam * (1 - (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * (1 / (1 + xiStar a1 a2 b1 b2))) ∧
      ∀ θ : ℝ, IsOptimalRisk lam (loanRate lam (b1 + b2) (∑ k, L k)) θ ↔
        θ = lam * (1 - 1 / 2 * ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) *
          (1 / (1 + xiStar a1 a2 b1 b2)))) ∧
    (xi a1 b1 < xi a2 b2 →
      xi a1 b1 < xiStar a1 a2 b1 b2 ∧ xiStar a1 a2 b1 b2 < xi a2 b2) := by
  obtain ⟨hlam, ha1, ha2, hb1, hb2, hn⟩ := hS
  obtain ⟨hex, hall⟩ := lemma_6a lam 0 (a1 + a2) (b1 + b2) (2 * n) hlam le_rfl (by linarith)
    (by linarith) (by linarith) (by omega)
  have hx : xiStar a1 a2 b1 b2 = xi (a1 + a2) (b1 + b2) := rfl
  refine ⟨hex, fun L hL => ?_, fun h => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hall L hL
    push_cast at h1 h2 h3 h4
    refine ⟨h1, by rw [h2, hx]; ring, by rw [h3, hx]; ring, fun θ => ?_⟩
    rw [h4 θ, hx]
    constructor <;> intro h <;> rw [h] <;> ring
  · unfold xi at h
    unfold xi xiStar
    rw [div_lt_div_iff₀ ha1 ha2] at h
    constructor
    · rw [div_lt_div_iff₀ ha1 (by linarith)]; nlinarith
    · rw [div_lt_div_iff₀ (by linarith) ha2]; nlinarith
