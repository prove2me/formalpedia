-- Prove2me | solution 2 for DiazModulus.recip_pi_log_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:57.801499+00:00
-- url     : https://prove2.me/submissions/c2a92262-1904-486b-8f7d-73fc4b767d0a

import Mathlib
import Theorems.Thm_Transcendence_quadratic_coeffs_eq_zero_of_transcendental
import Theorems.Thm_DiazModulus_four_exp_barrier_of_no_quadratic_relation
import Theorems.Thm_DiazModulus_pi_transcendental

namespace S7W2_recip_pi_log_four_exp_barrier

/-- `(πi)² = -π²` is transcendental, since `π` is. -/
theorem w_sq_transcendental : Transcendental ℚ ((((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2) := by
  intro h
  apply DiazModulus.pi_transcendental
  have e : ((Real.pi : ℝ) : ℂ) ^ 2 = -((((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  have h2 : IsAlgebraic ℚ (((Real.pi : ℝ) : ℂ) ^ 2) := by
    rw [e]
    exact h.neg
  exact h2.of_pow (by norm_num)

end S7W2_recip_pi_log_four_exp_barrier

open S7W2_recip_pi_log_four_exp_barrier in
/- Put `w = πi` and `e = (γ / w, w)`. A rational quadratic relation `Σ F k l · e k · e l = 0`,
multiplied by `w²`, reads `F₁₁ (w²)² + (F₀₁ + F₁₀) γ w² + F₀₀ γ² = 0`. Since `w²` is transcendental
and `γ ≠ 0` is algebraic, `quadratic_coeffs_eq_zero_of_transcendental` makes `F` alternating, and
`four_exp_barrier_of_no_quadratic_relation` applies. -/
theorem solution (γ : ℂ) (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (A : Fin 2 → Fin 2 → Fin 2 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = (A i j 0 : ℂ) * (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) + (A i j 1 : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw
  have hw0 : w ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  refine DiazModulus.four_exp_barrier_of_no_quadratic_relation ![γ / w, w] ?_ A M
    (fun i j => by rw [hM i j, Fin.sum_univ_two]; rfl) hdet
  intro F hF
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hF
  set t := γ / w with ht
  have hγ' : γ = t * w := by rw [ht, div_mul_cancel₀ γ hw0]
  have hrel : (F 1 1 : ℂ) * (w ^ 2) ^ 2 + (((F 0 1 + F 1 0 : ℚ) : ℂ) * γ) * w ^ 2
      + (F 0 0 : ℂ) * γ ^ 2 = 0 := by
    rw [hγ']
    push_cast
    linear_combination w ^ 2 * hF
  have halg : ∀ q : ℚ, IsAlgebraic ℚ (q : ℂ) := fun q => isAlgebraic_algebraMap q
  obtain ⟨h2, h1, h0⟩ := Transcendence.quadratic_coeffs_eq_zero_of_transcendental
    w_sq_transcendental ((halg _).mul (hγ.pow 2)) ((halg _).mul hγ) (halg _) hrel
  have e11 : F 1 1 = 0 := by exact_mod_cast h2
  have e01 : F 0 1 + F 1 0 = 0 := by
    have := (mul_eq_zero.mp h1).resolve_right hγ0
    exact_mod_cast this
  have e00 : F 0 0 = 0 := by
    have := (mul_eq_zero.mp h0).resolve_right (pow_ne_zero 2 hγ0)
    exact_mod_cast this
  intro k l
  fin_cases k <;> fin_cases l <;> simp [e11, e00] <;> linarith

#print axioms solution
