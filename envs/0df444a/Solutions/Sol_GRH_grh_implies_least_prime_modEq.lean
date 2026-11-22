-- Prove2me | solution 1 for GRH.grh_implies_least_prime_modEq
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mwm
-- created : 2026-11-21T22:28:10.518822+00:00
-- url     : https://prove2.me/submissions/7c237fba-e713-4367-9d80-5970e4e63265
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_GRH_grh_implies_thetaAP_square_root_log
import Theorems.Thm_GRH_least_prime_modEq_of_thetaAP_square_root_log

/-! # GRH implies Chowla's least-prime bound (parent)

Glue: `hGRH` gives the one-logarithm Chebyshev lower bound (Child A), which feeds the
balancing bridge (Child B) to produce the absolute constant K. -/

theorem solution
    (hGRH : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      (1 / 2 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    ∃ K : ℝ, ∀ (q : ℕ) (hq : 2 ≤ q) (a : ℕ) (ha : a.Coprime q),
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ K * (q : ℝ) ^ 2 * (Real.log q) ^ 2 := by
  obtain ⟨C, hC, hθ⟩ := GRH.grh_implies_thetaAP_square_root_log hGRH
  obtain ⟨K, -, hK⟩ := GRH.least_prime_modEq_of_thetaAP_square_root_log C hC hθ
  exact ⟨K, fun q hq a ha => hK q hq a ha⟩
