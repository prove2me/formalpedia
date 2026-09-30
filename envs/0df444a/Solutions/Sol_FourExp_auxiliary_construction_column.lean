-- Prove2me | solution 1 for FourExp.auxiliary_construction_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:04:27.937303+00:00
-- url     : https://prove2.me/submissions/7ebfd790-806e-47e8-a72c-935f22f0c68f

import Mathlib
import Theorems.Thm_FourExp_construction_growth
import Theorems.Thm_FourExp_construction_count_1973
import Theorems.Thm_FourExp_construction_core_column

/-!
# The auxiliary construction, in the column case

As in `FourExp.auxiliary_construction`, without the rank-one parametrization: `x` and `y` are
given. `FourExp.construction_core_column` gives `ω` and `k > 0`, and for each large `N` an
exponential polynomial whose non-zero derivatives on the 14-fold grid give small integer
polynomials; `FourExp.construction_growth` gives the growth conditions of
`σ₁ = k N² √(log N)` and `σ₂ = k N² / √(log N)` (glued below `N = 3`) with `a₁ = a₂ = 3`; and
`FourExp.construction_count_1973` gives the zero-count inequality with `λ = 1/20` on that grid.
-/

open Filter Topology

theorem solution :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
          Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1 →
      ∃ ω : ℂ, Transcendental ℚ ω ∧
        ∃ σ₁ σ₂ : ℝ → ℝ, StrictMono σ₁ ∧ StrictMono σ₂ ∧
          Tendsto σ₁ atTop atTop ∧ Tendsto σ₂ atTop atTop ∧
          ∃ a₁ a₂ : ℝ, 1 ≤ a₁ ∧ 1 ≤ a₂ ∧
            (∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x) ∧
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
  intro x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  -- the column, in the indexing of the construction
  have hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)) := by
    intro i
    fin_cases i
    · exact h₁₂
    · exact h₂₂
  obtain ⟨ω, hω, k, hk, hcore⟩ := FourExp.construction_core_column x₁ x₂ y₁ y₂ hx hy hexp₂ htr
  obtain ⟨hm₁, hm₂, ht₁, ht₂, h21, hg₁, hg₂⟩ := FourExp.construction_growth k hk
  refine ⟨ω, hω, _, _, hm₁, hm₂, ht₁, ht₂, 3, 3, by norm_num, by norm_num, h21, hg₁, hg₂,
    fun C => ?_⟩
  obtain ⟨N₁, hN₁⟩ := hcore C
  obtain ⟨N₂, hN₂⟩ := FourExp.construction_count_1973 (‖x₁‖ + ‖x₂‖) ‖y₁‖ ‖y₂‖ (by positivity)
    (norm_nonneg _) (norm_nonneg _)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨c, hc, himp⟩ := hN₁ N (lt_of_le_of_lt (le_max_left _ _) hN)
  exact ⟨_, _, _, _, _, c, hc, ⟨1 / 20, by norm_num, hN₂ N (lt_of_le_of_lt (le_max_right _ _) hN)⟩,
    himp⟩
