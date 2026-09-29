-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T15:50:19.353935+00:00
-- url     : https://prove2.me/submissions/9e4475f8-b031-4335-bddb-09a4c066d644
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_recip_pi_not_log_real_gamma

open Complex ComplexConjugate

namespace RealHalfAux

open DiazModulus

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ Qbar := mem_Qbar_iff.symm

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem alg_div {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z / w) := by
  rw [alg_iff_mem] at *
  exact Subfield.div_mem _ hz hw

theorem alg_neg {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (-z) := by
  rw [alg_iff_mem] at *
  exact Subfield.neg_mem _ hz

theorem alg_pow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℕ) : IsAlgebraic ℚ (z ^ n) := by
  rw [alg_iff_mem] at *
  exact Subfield.pow_mem _ hz n

end RealHalfAux

open RealHalfAux in
/-- The period-aligned branch needs only the real half of `(S)`: the number it produces,
`γ = -π(Im u + rπ)`, is real, with `γ/(πi) = i(Im u + rπ) = (u - ū)/2 + r·πi ∈ ℒ`. -/
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by
  intro u _ _ _ _ hirr hal _ hexp
  obtain ⟨r, hr0, halg⟩ := hal
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  set s : ℝ := u.im + (r : ℝ) * Real.pi with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    refine hirr ⟨-r, ?_⟩
    have : u.im = -((r : ℝ) * Real.pi) := by rw [hs_def] at h; linarith
    push_cast
    linarith [this]
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  set ν : ℂ := Complex.I * ((s : ℝ) : ℂ) with hν_def
  have hmul : (((2 * r.den : ℕ)) : ℂ) * ν =
      ((r.den : ℕ) : ℂ) * (u - conj u)
        + ((r.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.sub_conj, hν_def, hs_def]
    push_cast [Rat.cast_def]
    field_simp
  have hkey : Complex.exp ν ^ (2 * r.den) =
      (Complex.exp u / conj (Complex.exp u)) ^ r.den := by
    rw [← Complex.exp_nat_mul, hmul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_conj]
  have hexpν : IsAlgebraic ℚ (Complex.exp ν) := by
    refine IsAlgebraic.of_pow (n := 2 * r.den) (by positivity) ?_
    rw [hkey]
    exact alg_pow (alg_div hexp (alg_conj hexp)) r.den
  have heq : -(((Real.pi * s : ℝ)) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I) = ν := by
    rw [hν_def]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
  refine DiazModulus.recip_pi_not_log_real_gamma (-(((Real.pi * s : ℝ)) : ℂ))
    (alg_neg (by rw [hs_def] at halg ⊢; exact halg)) ?_ (by simp) (by rw [heq]; exact hexpν)
  simp only [neg_ne_zero, Complex.ofReal_ne_zero]
  exact mul_ne_zero hπ0 hs0

#print axioms solution
