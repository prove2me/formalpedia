-- Prove2me | solution 1 for DiazModulus.recip_pi_log_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T20:42:29.237982+00:00
-- url     : https://prove2.me/submissions/35ed3dd4-f0d8-4f99-b7ff-0d200715b897

import Mathlib
import Theorems.Thm_DiazModulus_det_zero_linear_forms_rank_one
import Theorems.Thm_DiazModulus_pi_transcendental

namespace RPLF

/-- Rationals are algebraic over `ℚ`. -/
theorem isAlg_rat (q : ℚ) : IsAlgebraic ℚ (q : ℂ) := by
  rw [show (q : ℂ) = algebraMap ℚ ℂ q by simp]
  exact isAlgebraic_algebraMap q

/-- `(πi)² = -π²` is transcendental, since `π` is. -/
theorem not_alg_w_sq : ¬ IsAlgebraic ℚ ((((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2) := by
  intro h
  have e : ((Real.pi : ℝ) : ℂ) ^ 2 = -((((Real.pi : ℝ) : ℂ) * Complex.I) ^ 2) := by
    rw [mul_pow, Complex.I_sq]
    ring
  have h2 : IsAlgebraic ℚ (((Real.pi : ℝ) : ℂ) ^ 2) := by
    rw [e]
    exact h.neg
  exact DiazModulus.pi_transcendental (h2.of_pow (by norm_num))

/-- If `t` is transcendental and `γ ≠ 0` is algebraic, then a relation
`P γ² + Q γ t + R t² = 0` with rational `P, Q, R` forces `P = Q = R = 0`. -/
theorem coeffs_eq_zero {γ t : ℂ} (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (ht : ¬ IsAlgebraic ℚ t) (P Q R : ℚ)
    (h : (P : ℂ) * γ ^ 2 + (Q : ℂ) * γ * t + (R : ℂ) * t ^ 2 = 0) :
    P = 0 ∧ Q = 0 ∧ R = 0 := by
  have hR : R = 0 := by
    by_contra hR
    apply ht
    have hR' : ((2 * R : ℚ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero hR
    -- `u = 2 R t + Q γ` satisfies `u² = (Q² - 4 R P) γ²`, so `u` is algebraic
    have hu2 : (((2 * R : ℚ) : ℂ) * t + (Q : ℂ) * γ) ^ 2
        = ((Q ^ 2 - 4 * R * P : ℚ) : ℂ) * γ ^ 2 := by
      push_cast
      linear_combination 4 * (R : ℂ) * h
    have hu : IsAlgebraic ℚ (((2 * R : ℚ) : ℂ) * t + (Q : ℂ) * γ) := by
      refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
      rw [hu2]
      exact (isAlg_rat _).mul (hγ.pow 2)
    have ht' : t = ((((2 * R : ℚ) : ℂ) * t + (Q : ℂ) * γ) - (Q : ℂ) * γ)
        * (((2 * R : ℚ) : ℂ))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hR']
      ring
    rw [ht']
    exact (hu.sub ((isAlg_rat Q).mul hγ)).mul (isAlg_rat _).inv
  have hR' : (R : ℂ) = 0 := by exact_mod_cast hR
  have hQ : Q = 0 := by
    by_contra hQ
    apply ht
    have hQ' : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ
    have h1 : γ * ((Q : ℂ) * t + (P : ℂ) * γ) = 0 := by
      linear_combination h - t ^ 2 * hR'
    have h2 : (Q : ℂ) * t + (P : ℂ) * γ = 0 := (mul_eq_zero.1 h1).resolve_left hγ0
    have ht' : t = -((P : ℂ) * γ) * ((Q : ℂ))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hQ']
      linear_combination h2
    rw [ht']
    exact ((isAlg_rat P).mul hγ).neg.mul (isAlg_rat Q).inv
  have hQ' : (Q : ℂ) = 0 := by exact_mod_cast hQ
  have hP : (P : ℂ) * γ ^ 2 = 0 := by
    linear_combination h - γ * t * hQ' - t ^ 2 * hR'
  refine ⟨?_, hQ, hR⟩
  exact_mod_cast (mul_eq_zero.1 hP).resolve_right (pow_ne_zero 2 hγ0)

end RPLF

open RPLF in
/-- Put `w = πi` and `λ = γ / w`, so `M i j = A i j 0 · λ + A i j 1 · w`.
Multiplying `det M = 0` by `w²` gives `P γ² + Q γ w² + R w⁴ = 0`, where `P, Q, R` are the
symmetrised coefficients of `X₀², X₀X₁, X₁²` in `det (Σ_k A i j k X_k)`.
Since `w² = -π²` is transcendental and `γ ≠ 0` is algebraic, `P = Q = R = 0`, which is the
hypothesis of `det_zero_linear_forms_rank_one` for `n = 2`. Its row (column) dependence of
the coefficient vectors transfers linearly to the rows (columns) of `M`. -/
theorem solution (γ : ℂ) (hγ : IsAlgebraic ℚ γ) (hγ0 : γ ≠ 0)
    (A : Fin 2 → Fin 2 → Fin 2 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = (A i j 0 : ℂ) * (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) + (A i j 1 : ℂ) * (((Real.pi : ℝ) : ℂ) * Complex.I))
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht := not_alg_w_sq
  set w : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw_def
  have hw : w ≠ 0 := mul_ne_zero hπ Complex.I_ne_zero
  set l : ℂ := γ / w with hl_def
  have hγl : γ = l * w := by
    rw [hl_def]
    field_simp
  -- `w² · det M = P γ² + Q γ w² + R w⁴`
  have key : ((A 0 0 0 * A 1 1 0 - A 0 1 0 * A 1 0 0 : ℚ) : ℂ) * γ ^ 2
      + ((A 0 0 0 * A 1 1 1 + A 0 0 1 * A 1 1 0 - A 0 1 0 * A 1 0 1 - A 0 1 1 * A 1 0 0 : ℚ) : ℂ)
        * γ * w ^ 2
      + ((A 0 0 1 * A 1 1 1 - A 0 1 1 * A 1 0 1 : ℚ) : ℂ) * (w ^ 2) ^ 2 = 0 := by
    rw [hM 0 0, hM 1 1, hM 0 1, hM 1 0] at hdet
    rw [hγl]
    push_cast
    linear_combination w ^ 2 * hdet
  obtain ⟨hP, hQ, hR⟩ := coeffs_eq_zero hγ hγ0 ht _ _ _ key
  have hdet' : ∀ k l : Fin 2,
      A 0 0 k * A 1 1 l + A 0 0 l * A 1 1 k = A 0 1 k * A 1 0 l + A 0 1 l * A 1 0 k := by
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · linear_combination 2 * hP
    · linear_combination hQ
    · linear_combination hQ
    · linear_combination 2 * hR
  rcases DiazModulus.det_zero_linear_forms_rank_one 2 A hdet' with
    ⟨p, q, hpq, h⟩ | ⟨p, q, hpq, h⟩
  · left
    refine ⟨p, q, hpq, fun j => ?_⟩
    have h0 : (p : ℂ) * (A 0 j 0 : ℂ) + (q : ℂ) * (A 1 j 0 : ℂ) = 0 := by exact_mod_cast h j 0
    have h1 : (p : ℂ) * (A 0 j 1 : ℂ) + (q : ℂ) * (A 1 j 1 : ℂ) = 0 := by exact_mod_cast h j 1
    rw [hM 0 j, hM 1 j]
    linear_combination l * h0 + w * h1
  · right
    refine ⟨p, q, hpq, fun i => ?_⟩
    have h0 : (p : ℂ) * (A i 0 0 : ℂ) + (q : ℂ) * (A i 1 0 : ℂ) = 0 := by exact_mod_cast h i 0
    have h1 : (p : ℂ) * (A i 0 1 : ℂ) + (q : ℂ) * (A i 1 1 : ℂ) = 0 := by exact_mod_cast h i 1
    rw [hM i 0, hM i 1]
    linear_combination l * h0 + w * h1

#print axioms solution
