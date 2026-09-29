-- Prove2me | solution 1 for Diaz.log_circles_alignment
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:24:29.807266+00:00
-- url     : https://prove2.me/submissions/8238c9a5-0521-47f6-81e8-1d37cfacf535

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {μ₁ μ₂ : ℂ} (h1 : μ₁ ≠ 0) {m c : ℚ}
    (hm : Complex.normSq μ₂ = (m : ℝ) * Complex.normSq μ₁)
    (halign : μ₂ = (c : ℂ) * μ₁ ∨ μ₂ = (c : ℂ) * conj μ₁) :
    m = c ^ 2 ∧ (m = 1 → μ₂ = μ₁ ∨ μ₂ = -μ₁ ∨ μ₂ = conj μ₁ ∨ μ₂ = -conj μ₁) := by
  have hn1 : Complex.normSq μ₁ ≠ 0 := by
    simpa using h1
  have hmc : m = c ^ 2 := by
    have hcn : Complex.normSq ((c : ℂ)) = (c : ℝ) ^ 2 := by
      simp [Complex.normSq_apply]; ring
    have hstep : ((m : ℝ)) * Complex.normSq μ₁ = ((c : ℝ)) ^ 2 * Complex.normSq μ₁ := by
      rw [← hm]
      rcases halign with hA | hA <;> rw [hA, Complex.normSq_mul, hcn]
      rw [Complex.normSq_conj]
    have hmr : (m : ℝ) = (c : ℝ) ^ 2 := mul_right_cancel₀ hn1 hstep
    exact_mod_cast hmr
  refine ⟨hmc, ?_⟩
  intro hm1
  have hc2 : (c - 1) * (c + 1) = 0 := by
    have hcc : c ^ 2 = 1 := by rw [← hmc, hm1]
    linear_combination hcc
  rcases mul_eq_zero.1 hc2 with h | h <;>
    [ (have hcv : c = 1 := by linarith); (have hcv : c = -1 := by linarith) ] <;>
    subst hcv <;> rcases halign with hA | hA <;> rw [hA] <;> push_cast <;> simp
