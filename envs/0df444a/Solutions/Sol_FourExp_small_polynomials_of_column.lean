-- Prove2me | solution 1 for FourExp.small_polynomials_of_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:57:23.838584+00:00
-- url     : https://prove2.me/submissions/29efc220-67be-47b9-ace3-7be5810fc47c

import Mathlib
import Theorems.Thm_FourExp_auxiliary_construction_column
import Theorems.Thm_FourExp_nonvanishing_derivative

/-!
# Small integer polynomials at `ω`, in the column case

As in `FourExp.small_polynomials_of_counterexample`: `FourExp.auxiliary_construction_column`
supplies, for each large `N`, an exponential polynomial whose zero count is exceeded on a grid of
points `a y₁ + b y₂`, and turns any non-zero derivative there into a small integer polynomial.
`FourExp.nonvanishing_derivative` supplies that non-zero derivative, since `x` and `y` are
`ℚ`-linearly independent. A choice for each `N` gives the sequence `P_N`.
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
            ∀ C : ℝ, ∃ N₀ : ℕ, ∃ P : ℕ → Polynomial ℤ, ∀ N : ℕ, N₀ < N →
              P N ≠ 0 ∧
              (∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
              ((P N).natDegree : ℝ) ≤ σ₂ N ∧
              ‖Polynomial.aeval ω (P N)‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
  intro x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  obtain ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, hC⟩ :=
    FourExp.auxiliary_construction_column x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  refine ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, fun C => ?_⟩
  obtain ⟨N₀, hN⟩ := hC C
  -- for each large `N`, a small polynomial
  have key : ∀ N : ℕ, N₀ < N → ∃ P : Polynomial ℤ, P ≠ 0 ∧
      (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
      (P.natDegree : ℝ) ≤ σ₂ N ∧
      ‖Polynomial.aeval ω P‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
    intro N hN'
    obtain ⟨S, T, R₁, R₂, S', c, hc, ⟨lam, hlam, hcount⟩, himp⟩ := hN N hN'
    obtain ⟨a, b, s, ha, hb, hs, hne⟩ :=
      FourExp.nonvanishing_derivative x₁ x₂ y₁ y₂ hx hy S T R₁ R₂ S' c hc lam hlam hcount
    exact himp a b s ha hb hs hne
  -- one choice for each `N`
  classical
  refine ⟨N₀, fun N => if h : N₀ < N then Classical.choose (key N h) else 0, fun N hN' => ?_⟩
  simp only [dif_pos hN']
  exact Classical.choose_spec (key N hN')
