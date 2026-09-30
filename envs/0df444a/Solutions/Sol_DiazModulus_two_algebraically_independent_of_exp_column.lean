-- Prove2me | solution 1 for DiazModulus.two_algebraically_independent_of_exp_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T07:48:58.698152+00:00
-- url     : https://prove2.me/submissions/952ea261-0e65-44d6-baf0-1f5d380df773

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_isAlgebraic_adjoin_of_not_algebraicIndependent_pair
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin
import Theorems.Thm_FourExp_small_polynomials_of_column
import Theorems.Thm_FourExp_transcendence_criterion

/-!
# Waldschmidt's theorem of 1973

Suppose that no two of the eight numbers `xᵢ`, `yⱼ`, `e^{xᵢyⱼ}` are algebraically independent.

* **One of them is transcendental.** `x₁ ≠ 0` and `y₂ ≠ 0`, since they belong to linearly
  independent pairs. If `x₁` and `y₂` were both algebraic, then `x₁ y₂` would be a non-zero
  algebraic number with `e^{x₁y₂}` algebraic, against Hermite–Lindemann. So one of them, `t`, is
  transcendental.
* **Transcendence degree one.** Every one of the eight numbers `s` forms with `t` a pair that is not
  algebraically independent, so `s` is algebraic over `ℚ[t]`
  (`Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair`). Hence
  `ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]` has transcendence degree at most one
  (`Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin`).
* **Contradiction.** As in `DiazModulus.four_exponentials_trdeg_one`: the analytic construction
  `FourExp.small_polynomials_of_column` gives a transcendental `ω` and integer polynomials that are
  too small at `ω`, and Gel'fond's criterion `FourExp.transcendence_criterion` makes `ω` algebraic.

No rank-one parametrization is needed: the hypothesis is already stated in `x`, `y` form.
-/

theorem solution :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      ∃ a ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
          Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
        ∃ b ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
            Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
          AlgebraicIndependent ℚ ![a, b] := by
  intro x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂
  by_contra hne
  -- one of `x₁`, `y₂` is transcendental, by Hermite–Lindemann
  have hx1 : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hy2 : y₂ ≠ 0 := by simpa using hy.ne_zero 1
  have hxy : Transcendental ℚ x₁ ∨ Transcendental ℚ y₂ := by
    by_contra h
    rw [not_or, Transcendental, Transcendental, not_not, not_not] at h
    exact DiazModulus.hermite_lindemann_holds (x₁ * y₂) (mul_ne_zero hx1 hy2) (h.1.mul h.2) h₁₂
  obtain ⟨t, ht8, ht⟩ : ∃ t ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
      Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ), Transcendental ℚ t :=
    hxy.elim (fun h => ⟨x₁, by simp, h⟩) (fun h => ⟨y₂, by simp, h⟩)
  -- the eight numbers are algebraic over `ℚ[t]`
  have halg : ∀ s ∈ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₁ * y₂),
      Complex.exp (x₂ * y₁), Complex.exp (x₂ * y₂)} : Set ℂ),
      IsAlgebraic ↥(Algebra.adjoin ℚ ({t} : Set ℂ)) s := fun s hs =>
    Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair ht
      fun h => hne ⟨t, ht8, s, hs, h⟩
  -- so the six numbers of the construction generate transcendence degree at most one
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
      Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1 := by
    refine Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin t _ fun s hs => halg s ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    tauto
  -- the analytic construction, and Gel'fond's criterion
  obtain ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, hC⟩ :=
    FourExp.small_polynomials_of_column x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  obtain ⟨N₀, P, hP⟩ := hC (max (10 + 1) ((4 + 1) * (a₁ * a₂)))
  exact hω (FourExp.transcendence_criterion ω 1 one_pos σ₁ σ₂ hm₁ hm₂ ht₁ ht₂ a₁ a₂ ha₁ ha₂
    h₂₁ hg₁ hg₂ N₀ P (fun N hN => (hP N hN).1) (fun N hN => (hP N hN).2.1)
    (fun N hN => (hP N hN).2.2.1) (fun N hN => (hP N hN).2.2.2))
