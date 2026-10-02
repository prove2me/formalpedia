-- Prove2me | solution 1 for DiazModulus.diaz_2007_qr2_of_trdeg_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T08:45:09.420272+00:00
-- url     : https://prove2.me/submissions/ac57f45c-3985-4ca6-b9b6-dc031e88ff35

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_log_mul_real_trichotomy_of_trdeg_one
import Theorems.Thm_DiazModulus_log_mul_imaginary_mixed_of_trdeg_one

open Complex ComplexConjugate

namespace R2_diaz_2007_qr2_of_trdeg_one

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

/-- The conjugate of a logarithm of an algebraic number is one too. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact hw.algHom cjQ

/-- `l̄₀ l₁ = |l₀|² (l₁ / l₀)`: the product and the quotient have the same argument. -/
theorem conj_mul_eq {l₀ l₁ : ℂ} (h : l₀ ≠ 0) :
    conj l₀ * l₁ = (Complex.normSq l₀ : ℂ) * (l₁ / l₀) := by
  rw [← Complex.mul_conj, mul_comm l₀ (conj l₀), mul_assoc, mul_div_assoc', mul_comm l₀ l₁,
    mul_div_assoc, div_self h, mul_one]

end R2_diaz_2007_qr2_of_trdeg_one

open R2_diaz_2007_qr2_of_trdeg_one in
theorem solution (l₀ l₁ : ℂ)
    (he₀ : IsAlgebraic ℚ (Complex.exp l₀)) (he₁ : IsAlgebraic ℚ (Complex.exp l₁))
    (h₀ : l₀.re ≠ 0 ∧ l₀.im ≠ 0) (h₁ : l₁.re ≠ 0 ∧ l₁.im ≠ 0)
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₀, l₁, conj l₀, conj l₁} : Set ℂ)) ≤ 1)
    (hax : (l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) :
    ∃ q : ℚ, l₁ / l₀ = q := by
  have hl₀ : l₀ ≠ 0 := fun h => h₀.1 (by rw [h, Complex.zero_re])
  have hl₁ : l₁ ≠ 0 := fun h => h₁.1 (by rw [h, Complex.zero_re])
  -- `λ := l̄₀`, `μ := l₁`: the adjoined set is the hypothesis's, reordered
  have htr' : Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({conj l₀, l₁, conj (conj l₀), conj l₁} : Set ℂ)) ≤ 1 := by
    have hset : ({conj l₀, l₁, conj (conj l₀), conj l₁} : Set ℂ)
        = {l₀, l₁, conj l₀, conj l₁} := by
      rw [Complex.conj_conj]; ext z; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rw [hset]; exact htr
  have hc₀ : conj l₀ ≠ 0 := (map_ne_zero _).2 hl₀
  have hkey : conj l₀ * l₁ = (Complex.normSq l₀ : ℂ) * (l₁ / l₀) := conj_mul_eq hl₀
  rcases hax with h | h
  · -- `l₁ / l₀` real, hence so is `l̄₀ l₁`: the axis branches would put `l̄₀` on an axis
    have hreal : (conj l₀ * l₁).im = 0 := by rw [hkey, Complex.im_ofReal_mul, h, mul_zero]
    rcases DiazModulus.log_mul_real_trichotomy_of_trdeg_one (conj l₀) l₁ hc₀ hl₁
        (exp_conj_alg he₀) he₁ htr' hreal with ⟨h2, -⟩ | ⟨h2, -⟩ | ⟨q, hq⟩
    · exact (h₀.2 (by simpa using h2)).elim
    · exact (h₀.1 (by simpa using h2)).elim
    · -- `l₁ = q · conj (conj l₀) = q l₀`
      refine ⟨q, ?_⟩
      rw [hq, Complex.conj_conj, mul_div_assoc, div_self hl₀, mul_one]
  · -- `l₁ / l₀` purely imaginary, hence so is `l̄₀ l₁`: then `l̄₀` would lie on an axis
    have himag : (conj l₀ * l₁).re = 0 := by rw [hkey, Complex.re_ofReal_mul, h, mul_zero]
    rcases DiazModulus.log_mul_imaginary_mixed_of_trdeg_one (conj l₀) l₁ hc₀ hl₁
        (exp_conj_alg he₀) he₁ htr' himag with ⟨h2, -⟩ | ⟨h2, -⟩
    · exact (h₀.2 (by simpa using h2)).elim
    · exact (h₀.1 (by simpa using h2)).elim

#print axioms solution
