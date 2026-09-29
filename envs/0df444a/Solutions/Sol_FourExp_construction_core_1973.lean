-- Prove2me | solution 1 for FourExp.construction_core_1973
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-16T12:30:09.89799+00:00
-- url     : https://prove2.me/submissions/d2a23e9f-aa9e-4f36-97bb-676018f9c491
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_FourExp_trdeg_one_presentation
import Theorems.Thm_FourExp_auxiliary_function
import Theorems.Thm_FourExp_extrapolation
import Theorems.Thm_FourExp_norm_to_polynomial

theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1) :
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
    FourExp.trdeg_one_presentation x₁ x₂ y₁ y₂ hx hy hexp htr
  obtain ⟨κ, hκ, N₃, h3⟩ := FourExp.auxiliary_function x₁ x₂ y₁ y₂ ω ω₁ hω Q hQm hQd hQroot hQmin
    D E G H hD hE hG hH
  obtain ⟨κ', hκ', N₄, h4⟩ := FourExp.extrapolation x₁ x₂ y₁ y₂ hy κ hκ
  obtain ⟨k, hk, h5⟩ := FourExp.norm_to_polynomial x₁ x₂ y₁ y₂ ω ω₁ hω Q hQm hQd hQroot hQmin
    D E G H hD hE hG hH κ κ' hκ hκ'
  refine ⟨ω, hω, k, hk, fun C => ?_⟩
  obtain ⟨N₅, h5C⟩ := h5 C
  refine ⟨max N₃ (max N₄ N₅), fun N hN => ?_⟩
  obtain ⟨M, hM, q, hq, hc0, hcb, hvan⟩ := h3 N (lt_of_le_of_lt (le_max_left _ _) hN)
  refine ⟨_, hc0, fun a b s ha hb hs hne => ?_⟩
  exact h5C N (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN) M hM q hq
    a b s ha hb hs hne
    (h4 N (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN) _ hcb hvan s hs a b ha hb)
