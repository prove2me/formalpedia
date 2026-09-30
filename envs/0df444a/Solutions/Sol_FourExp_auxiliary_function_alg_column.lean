-- Prove2me | solution 1 for FourExp.auxiliary_function_alg_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:22:22.905313+00:00
-- url     : https://prove2.me/submissions/e1f444e1-9206-4e0f-9289-97101891ed27

import Mathlib
import Theorems.Thm_FourExp_aux_linear_system_column
import Theorems.Thm_FourExp_siegel_aux

/-!
# Siegel's auxiliary function, in the column case

As in `FourExp.auxiliary_function_alg`, in two steps.

* `FourExp.aux_linear_system_column` turns the reduced presentation `hpres` into, for large `N`,
  an `M ≤ κ₁ S` and an integer linear system with at most half as many equations as unknowns and
  coefficients at most `e^(κ₁ N² √(log N))`, whose solutions make `F_q⁽ᵐ⁾(a y₁ + b y₂)` vanish for
  `a < t₁`, `b < t₂`, `m < S`.
* `FourExp.siegel_aux` solves that system with Siegel's lemma, using the minimality of `Q` for the
  non-zero coefficient `c_{ijk} = ∑ q_{ijkμν} ω^μ ω₁^ν`, and bounds `q` and `c` by
  `e^(κ N² √(log N))` with `κ ≥ κ₁`.

Taking `N₀` past both thresholds, the solution `q` gives the auxiliary function.
-/

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (ω ω₁ : ℂ) (Q : Polynomial (Polynomial ℤ)) (hQd : 0 < Q.natDegree)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (hpres : ∃ c : ℕ, ∀ S T M a b m : ℕ, ∃ Λ : ℂ, Λ ≠ 0 ∧
      ‖Λ‖ ≤ (c : ℝ) ^ (c * (1 + m + S + T * (a + b))) ∧
      ∃ R : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → Polynomial (Polynomial ℤ),
        (∀ i j k μ ν, (R i j k μ ν).natDegree < Q.natDegree) ∧
        (∀ i j k μ ν, ∑ r ∈ (R i j k μ ν).support, ∑ h ∈ ((R i j k μ ν).coeff r).support,
            (((R i j k μ ν).coeff r).coeff h).natAbs ≤
          c ^ (c * (1 + m + S + T * (a + b))) * (1 + m + S + T + a + b) ^ (c * (1 + m + S))) ∧
        (∀ i j k μ ν r, ((R i j k μ ν).coeff r).natDegree ≤ M + c * (1 + m + S + T * a)) ∧
        ∀ q : Fin S → Fin T → Fin T → Fin M → Fin Q.natDegree → ℤ,
          Λ * iteratedDeriv m (fun z : ℂ => ∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T,
              (∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
                ((q i j k μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) * z ^ (i : ℕ) *
                Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k : ℕ) : ℂ) * x₂) * z))
            ((a : ℂ) * y₁ + (b : ℂ) * y₂) =
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁
            (∑ i : Fin S, ∑ j : Fin T, ∑ k : Fin T, ∑ μ : Fin M, ∑ ν : Fin Q.natDegree,
              Polynomial.C (Polynomial.C (q i j k μ ν)) * R i j k μ ν)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ ∧
      ∃ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M → Fin Q.natDegree → ℤ,
        (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (∃ i j k', (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' ≠ 0) ∧
        (∀ i j k', ‖(fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
        (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) * Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
          iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊, ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) * ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) := by
  -- the linear system, from the reduced presentation
  obtain ⟨κ₁, hκ₁, N₁, hsys⟩ := FourExp.aux_linear_system_column x₁ x₂ y₁ y₂ ω ω₁ Q hpres
  -- Siegel's lemma solves it
  obtain ⟨κ, hκle, N₂, hsieg⟩ := FourExp.siegel_aux ω ω₁ Q hQd hQmin κ₁ hκ₁
  refine ⟨κ, lt_of_lt_of_le hκ₁ hκle, max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨M, hM0, hMle, R, hR, B, hBb, hvan⟩ := hsys N (lt_of_le_of_lt (le_max_left _ _) hN)
  obtain ⟨q, hBq, hqb, hc0, hcb⟩ :=
    hsieg N (lt_of_le_of_lt (le_max_right _ _) hN) M hM0 hMle R hR B hBb
  exact ⟨M, hMle.trans (mul_le_mul_of_nonneg_right hκle (Nat.cast_nonneg _)), q, hqb, hc0, hcb,
    hvan q hBq⟩
