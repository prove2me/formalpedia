-- Prove2me | solution 1 for FourExp.auxiliary_construction
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-15T06:23:25.212308+00:00
-- url     : https://prove2.me/submissions/a8915f83-de27-4217-9c2b-878eb079ab3f

import Mathlib
import Theorems.Thm_FourExp_rank_one_parametrization
import Theorems.Thm_FourExp_construction_growth
import Theorems.Thm_FourExp_construction_count
import Theorems.Thm_FourExp_construction_core

open Filter Topology

theorem solution :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0) →
      ¬ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) →
      ∃ ω : ℂ, Transcendental ℚ ω ∧
        ∃ σ₁ σ₂ : ℝ → ℝ, StrictMono σ₁ ∧ StrictMono σ₂ ∧
          Tendsto σ₁ atTop atTop ∧ Tendsto σ₂ atTop atTop ∧
          ∃ a₁ a₂ : ℝ, 1 ≤ a₁ ∧ 1 ≤ a₂ ∧
            (∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x) ∧
          ∃ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] ∧ LinearIndependent ℚ ![y₁, y₂] ∧
            ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
              ∃ (S T R₁ R₂ S' : ℕ) (c : Fin S → Fin T → Fin T → ℂ), (∃ i j k, c i j k ≠ 0) ∧
              (∃ lam : ℝ, 0 < lam ∧ (((S * T * T : ℕ) : ℝ) / lam
              + 2 * (1 + ((S * T * T : ℕ) : ℝ) ^ lam) / (lam * Real.log ((S * T * T : ℕ) : ℝ))
                * (1 + ((R₁ : ℝ) * ‖y₁‖ + (R₂ : ℝ) * ‖y₂‖) * ((T : ℝ) * (‖x₁‖ + ‖x₂‖)))
            ≤ ((R₁ * R₂ * S' : ℕ) : ℝ))) ∧
              ∀ a b s : ℕ, a < R₁ → b < R₂ → s < S' →
                iteratedDeriv s (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              c i j k * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
                  ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
                ∃ P : Polynomial ℤ, P ≠ 0 ∧
                  (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
                  (P.natDegree : ℝ) ≤ σ₂ N ∧
                  ‖Polynomial.aeval ω P‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
  intro l₁₁ l₁₂ l₂₁ l₂₂ e₁₁ e₁₂ e₂₁ e₂₂ n₁₁ n₁₂ n₂₁ n₂₂ hdet htr hrows hcols
  obtain ⟨x₁, x₂, y₁, y₂, hx, hy, hexp, htr'⟩ :=
    FourExp.rank_one_parametrization l₁₁ l₁₂ l₂₁ l₂₂ e₁₁ e₁₂ e₂₁ e₂₂ n₁₁ n₁₂ n₂₁ n₂₂ hdet htr
      hrows hcols
  obtain ⟨ω, hω, k, hk, hcore⟩ := FourExp.construction_core x₁ x₂ y₁ y₂ hx hy hexp htr'
  obtain ⟨hm₁, hm₂, ht₁, ht₂, h21, hg₁, hg₂⟩ := FourExp.construction_growth k hk
  refine ⟨ω, hω, _, _, hm₁, hm₂, ht₁, ht₂, 3, 3, by norm_num, by norm_num, h21, hg₁, hg₂,
    x₁, x₂, y₁, y₂, hx, hy, fun C => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hcore C
  obtain ⟨N₂, hN₂⟩ := FourExp.construction_count (‖x₁‖ + ‖x₂‖) ‖y₁‖ ‖y₂‖ (by positivity)
    (norm_nonneg _) (norm_nonneg _)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨c, hc, himp⟩ := hN₁ N (lt_of_le_of_lt (le_max_left _ _) hN)
  exact ⟨_, _, _, _, _, c, hc, ⟨1 / 20, by norm_num, hN₂ N (lt_of_le_of_lt (le_max_right _ _) hN)⟩,
    himp⟩
