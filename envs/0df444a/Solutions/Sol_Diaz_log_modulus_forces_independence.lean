-- Prove2me | solution 1 for Diaz.log_modulus_forces_independence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:30:09.601972+00:00
-- url     : https://prove2.me/submissions/06461702-15e0-4fde-8e56-0e16b4ea47d0

import Mathlib

open ComplexConjugate

theorem solution {K : Subfield ℂ}
    (hKconj : ∀ z : ℂ, z ∈ K → conj z ∈ K)
    (hMaster : ∀ μ₁ ν₁ μ₂ ν₂ : ℂ,
      Complex.exp μ₁ ∈ K → Complex.exp ν₁ ∈ K → Complex.exp μ₂ ∈ K → Complex.exp ν₂ ∈ K →
      μ₁ ≠ 0 → ν₁ ≠ 0 → μ₂ ≠ 0 → ν₂ ≠ 0 →
      ∀ m : ℚ, m ≠ 0 → μ₂ * ν₂ = (m : ℂ) * (μ₁ * ν₁) →
      ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * μ₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * ν₁))
      ∨ ((∃ c : ℚ, c ≠ 0 ∧ μ₂ = (c : ℂ) * ν₁) ∧ (∃ c : ℚ, c ≠ 0 ∧ ν₂ = (c : ℂ) * μ₁))
      ∨ 2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({μ₁, ν₁, μ₂, ν₂} : Set ℂ)))
    {lam : ℂ}
    (hlam : Complex.exp lam ∈ K) (hlam0 : lam ≠ 0) (hlamR : lam.im ≠ 0)
    (hmod : Complex.exp ((‖lam‖ : ℝ) : ℂ) ∈ K) :
    2 ≤ Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)) := by
  have hconjmem : Complex.exp (conj lam) ∈ K := by
    rw [Complex.exp_conj]; exact hKconj _ hlam
  have hcj0 : conj lam ≠ 0 := by
    simpa using hlam0
  have hmod0 : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using hlam0
  have hprod : ((‖lam‖ : ℝ) : ℂ) * ((‖lam‖ : ℝ) : ℂ)
      = ((1 : ℚ) : ℂ) * (lam * conj lam) := by
    rw [Rat.cast_one, one_mul, Complex.mul_conj]
    norm_cast
    exact Complex.norm_mul_self_eq_normSq lam
  have hset : ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ), ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)
      = ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ) := by
    ext x; simp; try tauto
  rcases hMaster lam (conj lam) ((‖lam‖ : ℝ) : ℂ) ((‖lam‖ : ℝ) : ℂ)
      hlam hconjmem hmod hmod hlam0 hcj0 hmod0 hmod0 1 one_ne_zero hprod with
    ⟨⟨c, hc0, hc⟩, -⟩ | ⟨⟨c, hc0, hc⟩, -⟩ | htd2
  · exfalso
    apply hlamR
    have := congrArg Complex.im hc
    simp at this
    rcases this with h | h
    · exact absurd h (by exact_mod_cast hc0)
    · exact h
  · exfalso
    apply hlamR
    have := congrArg Complex.im hc
    simp at this
    rcases this with h | h
    · exact absurd h (by exact_mod_cast hc0)
    · exact h
  · rwa [hset] at htd2
