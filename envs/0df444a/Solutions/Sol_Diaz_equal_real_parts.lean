-- Prove2me | solution 1 for Diaz.equal_real_parts
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:22:47.528917+00:00
-- url     : https://prove2.me/submissions/a1f145dc-febe-47a5-bf0a-c1e029820c53

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {μ₁ μ₂ : ℂ} {m : ℚ}
    (hre : μ₂.re = μ₁.re)
    (hm : Complex.normSq μ₂ = (m : ℝ) * Complex.normSq μ₁) :
    (1 - (m : ℝ)) * μ₁.re ^ 2 + μ₂.im ^ 2 - (m : ℝ) * μ₁.im ^ 2 = 0
      ∧ (m = 1 → μ₂ = μ₁ ∨ μ₂ = conj μ₁) := by
  simp only [Complex.normSq_apply] at hm
  rw [hre] at hm
  refine ⟨by linear_combination hm, ?_⟩
  intro hm1
  subst hm1
  push_cast at hm
  have hsq : (μ₂.im - μ₁.im) * (μ₂.im + μ₁.im) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 hsq with h | h
  · left; apply Complex.ext hre (by linarith [sub_eq_zero.1 h])
  · right; apply Complex.ext (by simpa using hre) (by simp; linarith)
