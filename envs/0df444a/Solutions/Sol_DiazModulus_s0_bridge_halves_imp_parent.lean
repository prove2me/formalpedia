-- Prove2me | solution 1 for DiazModulus.s0_bridge_halves_imp_parent
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:16:34.596398+00:00
-- url     : https://prove2.me/submissions/07ddaf86-a95f-4c70-96f2-96fb0bed8282

import Mathlib

open ComplexConjugate in
theorem solution
    (hI : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.re = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))))
    (hR : ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 → γ.im = 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)))) :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  intro γ hγ h0 hexp
  by_cases him : γ.im = 0
  · exact hR γ hγ h0 him hexp
  let f : ℂ →ₐ[ℚ] ℂ := Complex.conjAe.toAlgHom.restrictScalars ℚ
  have hf : ∀ z : ℂ, f z = conj z := fun z => rfl
  have hcγ : IsAlgebraic ℚ (conj γ) := by
    rw [← hf]; exact hγ.algHom f
  have hδ : IsAlgebraic ℚ (γ - conj γ) := hγ.sub hcγ
  have hδ0 : γ - conj γ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact him (by linarith)
  have hδre : (γ - conj γ).re = 0 := by simp
  apply hI _ hδ hδ0 hδre
  have hπ : (((Real.pi : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : Complex.exp ((γ - conj γ) / (((Real.pi : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I)) *
        conj (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    rw [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I]
    field_simp
    ring
  rw [key]
  refine hexp.mul ?_
  rw [← hf]; exact hexp.algHom f
