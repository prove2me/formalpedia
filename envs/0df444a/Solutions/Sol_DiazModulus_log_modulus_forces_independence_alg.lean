-- Prove2me | solution 1 for DiazModulus.log_modulus_forces_independence_alg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T12:53:11.311369+00:00
-- url     : https://prove2.me/submissions/6c1a7ae3-b0b2-4c98-aa2c-c36f3467f1d7

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_log_pair_rigid_of_trdeg_one

open Complex ComplexConjugate

/-! # `log_modulus_forces_independence` for algebraic exponentials

Apply `log_pair_rigid_of_trdeg_one` to `u = λ`, `v = |λ|`: `|λ|·|λ| = 1 · λλ̄`. If `λ, λ̄, |λ|` had
transcendence degree at most 1, it would give `|λ| = qλ` or `|λ| = qλ̄` with `q` rational, and `q ≠ 0` since
`|λ| ≠ 0`; taking imaginary parts, `λ` would be real. -/

open DiazModulus in
theorem solution {lam : ℂ}
    (hlam : IsAlgebraic ℚ (Complex.exp lam)) (hlamR : lam.im ≠ 0)
    (hmod : IsAlgebraic ℚ (Complex.exp ((‖lam‖ : ℝ) : ℂ))) :
    2 ≤ Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)) := by
  have hlam0 : lam ≠ 0 := by
    rintro rfl; exact hlamR (by simp)
  have hmod0 : ((‖lam‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using hlam0
  have hprod : lam * conj lam
      = ((1 : ℚ) : ℂ) * (((‖lam‖ : ℝ) : ℂ) * conj ((‖lam‖ : ℝ) : ℂ)) := by
    rw [Rat.cast_one, one_mul, Complex.conj_ofReal, Complex.mul_conj]
    norm_cast
    exact (Complex.norm_mul_self_eq_normSq lam).symm
  have hset : ({lam, ((‖lam‖ : ℝ) : ℂ), conj lam, conj ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)
      = ({lam, conj lam, ((‖lam‖ : ℝ) : ℂ)} : Set ℂ) := by
    rw [Complex.conj_ofReal]; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  by_contra hlt
  have hle : Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({lam, ((‖lam‖ : ℝ) : ℂ), conj lam, conj ((‖lam‖ : ℝ) : ℂ)} : Set ℂ)) ≤ 1 := by
    rw [hset]
    by_contra h1
    apply hlt
    have h2 := Order.succ_le_of_lt (lt_of_not_ge h1)
    have h3 : Order.succ (1 : Cardinal) = 2 := by
      have := Cardinal.succ_natCast 1
      simpa [one_add_one_eq_two] using this
    rwa [h3] at h2
  obtain ⟨q, hq | hq⟩ :=
    log_pair_rigid_of_trdeg_one lam ((‖lam‖ : ℝ) : ℂ) hlam0 hmod0 hlam hmod 1 hprod hle
  all_goals
    have hq0 : q ≠ 0 := by rintro rfl; exact hmod0 (by simpa using hq)
    have := congrArg Complex.im hq
    simp at this
    rcases this with h | h
    · exact hq0 h
    · exact hlamR (by linarith)
