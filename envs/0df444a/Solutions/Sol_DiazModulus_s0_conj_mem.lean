-- Prove2me | solution 1 for DiazModulus.s0_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:48:06.186215+00:00
-- url     : https://prove2.me/submissions/b35dac39-480f-4412-abe2-8b480c53455e

import Mathlib

theorem dm1afabb12_conj_alg {x : ℂ} (h : IsAlgebraic ℚ x) : IsAlgebraic ℚ (starRingEnd ℂ x) :=
  h.algHom (starRingEnd ℂ).toRatAlgHom

theorem dm1afabb12_key (γ : ℂ) :
    Complex.exp ((starRingEnd ℂ γ) / (((Real.pi : ℝ) : ℂ) * Complex.I)) =
      (starRingEnd ℂ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg, map_div₀, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  congr 1
  rw [mul_neg, div_neg, neg_neg]

theorem solution :
    ∀ γ : ℂ, IsAlgebraic ℚ γ →
      IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) →
      IsAlgebraic ℚ (starRingEnd ℂ γ) ∧
        IsAlgebraic ℚ (Complex.exp ((starRingEnd ℂ γ) / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ he
  refine ⟨dm1afabb12_conj_alg hγ, ?_⟩
  rw [dm1afabb12_key]
  exact (dm1afabb12_conj_alg he).inv
