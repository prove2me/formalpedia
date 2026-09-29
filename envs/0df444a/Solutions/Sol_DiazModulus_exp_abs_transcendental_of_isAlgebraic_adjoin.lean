-- Prove2me | solution 1 for DiazModulus.exp_abs_transcendental_of_isAlgebraic_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:16:17.275715+00:00
-- url     : https://prove2.me/submissions/5439b4c3-04f2-4d7d-a983-1a46e8f90110

import Mathlib
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_Transcendence_trdeg_adjoin_le_one_of_isAlgebraic_adjoin

open ComplexConjugate

namespace S7W1_exp_abs_isAlgebraic_adjoin

/-- `ℒ` is stable under conjugation: `exp (conj w) = conj (exp w)`, and conjugation is a
`ℚ`-algebra homomorphism of `ℂ`. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]
  exact hw.algHom (starRingEnd ℂ).toRatAlgHom

/-- `|λ| |λ| = λ̄ λ`, the vanishing of the determinant of `[[|λ|, λ̄], [λ, |λ|]]`. -/
theorem norm_mul_norm (lam : ℂ) :
    ((‖lam‖ : ℝ) : ℂ) * ((‖lam‖ : ℝ) : ℂ) = conj lam * lam := by
  rw [mul_comm (conj lam), Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

end S7W1_exp_abs_isAlgebraic_adjoin

open S7W1_exp_abs_isAlgebraic_adjoin in
theorem solution (lam x : ℂ)
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (him : lam.im ≠ 0)
    (hl : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) lam)
    (hc : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) (conj lam)) :
    Transcendental ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ)) := by
  -- Four exponentials in transcendence degree one on `[[|λ|, λ̄], [λ, |λ|]]`.
  intro hr
  have hl0 : lam ≠ 0 := fun h => him (by simp [h])
  have hcl0 : conj lam ≠ 0 := (map_ne_zero _).2 hl0
  have hr0 : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hl0)
  have hrr := norm_mul_norm lam
  -- `|λ|` is algebraic over `ℚ[x]`, since `|λ|² = λ̄ λ` is.
  have hrA : IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ((‖lam‖ : ℝ) : ℂ) :=
    IsAlgebraic.of_pow two_pos (by rw [sq, hrr]; exact hc.mul hl)
  have htr := Transcendence.trdeg_adjoin_le_one_of_isAlgebraic_adjoin x
    ({((‖lam‖ : ℝ) : ℂ), conj lam, lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ) (by
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> assumption)
  -- `a |λ| + b λ = 0` forces `b = 0` (imaginary part, `|λ|` real), then `a = 0`.
  have key : ∀ a b : ℚ, ¬(a = 0 ∧ b = 0) →
      (a : ℂ) * ((‖lam‖ : ℝ) : ℂ) + (b : ℂ) * lam = 0 → False := by
    intro a b hab h
    have hb : b = 0 := by simpa [him] using congrArg Complex.im h
    subst hb
    exact hab ⟨by simpa [hr0] using h, rfl⟩
  rcases DiazModulus.four_exponentials_trdeg_one _ _ _ _ hr (exp_conj_alg hlam) hlam hr
      hr0 hcl0 hl0 hr0 hrr htr with ⟨a, b, hab, h1, -⟩ | ⟨a, b, hab, -, h2⟩
  · exact key a b hab h1
  · exact key b a (fun h => hab h.symm) (by linear_combination h2)

#print axioms solution
