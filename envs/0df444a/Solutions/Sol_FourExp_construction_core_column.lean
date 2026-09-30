-- Prove2me | solution 1 for FourExp.construction_core_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:14:14.931254+00:00
-- url     : https://prove2.me/submissions/7ea6e616-ba09-4224-98cc-2fb70b1dcae5

import Mathlib
import Theorems.Thm_FourExp_trdeg_one_presentation_column
import Theorems.Thm_FourExp_exists_iteratedDeriv_reduced_presentation_column
import Theorems.Thm_FourExp_auxiliary_function_alg_column
import Theorems.Thm_FourExp_extrapolation
import Theorems.Thm_FourExp_norm_to_polynomial_alg_column

/-!
# The core of the construction, in the column case

As in `FourExp.construction_core_1973`, in four steps.

* `FourExp.trdeg_one_presentation_column` presents the data over one integral model
  `Q(ω, ω₁) = 0`, with `ω` transcendental.
* `FourExp.exists_iteratedDeriv_reduced_presentation_column` presents the derivatives of the
  auxiliary function at the grid points, with `X`-degrees `M + c (1 + m + S + T a)`. Its conclusion
  is the hypothesis `hpres` of the Siegel and norm steps.
* `FourExp.auxiliary_function_alg_column` (Siegel) gives integer unknowns `q` that make the
  auxiliary function vanish to order `S` on the grid `t₁ × t₂`, and `FourExp.extrapolation` makes
  its derivatives small on the 14-fold grid.
* `FourExp.norm_to_polynomial_alg_column` turns a non-zero small derivative into a small integer
  polynomial at `ω`.
-/

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
      Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1) :
    ∃ ω : ℂ, Transcendental ℚ ω ∧ ∃ k : ℝ, 0 < k ∧
      ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
        ∃ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ, (∃ i j k', c i j k' ≠ 0) ∧
          ∀ a b s : ℕ, a < (14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) → b < (14 * ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊) → s < (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ / 2) →
            iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
            ∃ P : Polynomial ℤ, P ≠ 0 ∧
              (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
              (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
              ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 * Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ)))))) := by
  obtain ⟨ω, ω₁, hω, Q, hQm, hQd, hQroot, hQmin, D, E, G, H, hD, hE, hG, hH⟩ :=
    FourExp.trdeg_one_presentation_column x₁ x₂ y₁ y₂ hx hy hexp₂ htr
  have hpres := FourExp.exists_iteratedDeriv_reduced_presentation_column x₁ x₂ y₁ y₂ hexp₂ ω ω₁
    Q hQm hQroot D E G H hD hE hG hH
  obtain ⟨κ, hκ, N₃, h3⟩ :=
    FourExp.auxiliary_function_alg_column x₁ x₂ y₁ y₂ ω ω₁ Q hQd hQmin hpres
  obtain ⟨κ', hκ', N₄, h4⟩ := FourExp.extrapolation x₁ x₂ y₁ y₂ hy κ hκ
  obtain ⟨k, hk, h5⟩ := FourExp.norm_to_polynomial_alg_column x₁ x₂ y₁ y₂ ω ω₁ Q hQm hQroot
    hQmin hpres κ κ' hκ hκ'
  refine ⟨ω, hω, k, hk, fun C => ?_⟩
  obtain ⟨N₅, h5C⟩ := h5 C
  refine ⟨max N₃ (max N₄ N₅), fun N hN => ?_⟩
  obtain ⟨M, hM, q, hq, hc0, hcb, hvan⟩ := h3 N (lt_of_le_of_lt (le_max_left _ _) hN)
  refine ⟨_, hc0, fun a b s ha hb hs hne => ?_⟩
  exact h5C N (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN) M hM q hq
    a b s ha hb hs hne
    (h4 N (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN) _ hcb hvan s hs a b ha hb)
