-- Prove2me | solution 2 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T15:50:20.192912+00:00
-- url     : https://prove2.me/submissions/ec05abe1-709f-4d00-a3a1-c1d3f362e3c2
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
/-- The period-free branch with `π·Im u` algebraic needs only the real half of `(S)`: the number
it produces, `γ = -π Im u`, is real, with `γ/(πi) = i Im u = (u - ū)/2 ∈ ℒ`. -/
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (¬ ∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ) →
      Transcendental ℚ (Complex.exp u) := by
  intro u _ _ _ _ hirr _ halg hexp
  have hpi0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hs0 : u.im ≠ 0 := by
    intro h
    refine hirr ⟨0, ?_⟩
    rw [h]
    simp
  have hmul : (2 : ℂ) * (Complex.I * ((u.im : ℝ) : ℂ)) = u - conj u := by
    rw [Complex.sub_conj]; push_cast; ring
  have hkey : Complex.exp (Complex.I * ((u.im : ℝ) : ℂ)) ^ (2 : ℕ)
      = Complex.exp u / conj (Complex.exp u) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    rw [hmul, Complex.exp_sub, Complex.exp_conj]
  have hexpv : IsAlgebraic ℚ (Complex.exp (Complex.I * ((u.im : ℝ) : ℂ))) := by
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rw [hkey]
    exact alg_div hexp (alg_conj hexp)
  have hid : -(((Real.pi * u.im : ℝ)) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I)
      = Complex.I * ((u.im : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  refine DiazModulus.recip_pi_not_log_real_gamma (-(((Real.pi * u.im : ℝ)) : ℂ))
    (alg_neg halg) ?_ (by simp) (by rw [hid]; exact hexpv)
  simp only [neg_ne_zero, Complex.ofReal_ne_zero]
  exact mul_ne_zero hpi0 hs0

#print axioms solution
