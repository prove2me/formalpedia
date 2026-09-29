-- Prove2me | solution 1 for Diaz.salem_quartic_relations
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:27.85462+00:00
-- url     : https://prove2.me/submissions/11a10a41-f280-4e57-b039-ee2ea1b9800e

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem solution {t s : ℂ} (ht : t ≠ 0) (hs : s ≠ 0)
    (htR : t.im = 0) (hsI : s.re = 0)
    (hGS : IsAlgebraic ℚ (s / t) → ∃ r : ℚ, s / t = (r : ℂ))
    {A B C : ℚ} (h : (A : ℂ) * t ^ 2 + (B : ℂ) * (t * s) + (C : ℂ) * s ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  have htre : t.re ≠ 0 := fun hz => ht (by apply Complex.ext <;> simp [hz, htR])
  have hsim : s.im ≠ 0 := fun hz => hs (by apply Complex.ext <;> simp [hsI, hz])
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  simp [pow_two, Complex.mul_re, Complex.mul_im, htR, hsI] at hR hI
  have hB : B = 0 := by tauto
  have h0 : (A : ℂ) * t ^ 2 + (C : ℂ) * s ^ 2 = 0 := by
    rw [hB] at h; push_cast at h; linear_combination h
  -- Gelfond–Schneider step: `C ≠ 0` makes `s / t` algebraic, hence rational, hence real.
  have aux : C ≠ 0 → False := by
    intro hC
    have hCne : ((C : ℂ)) ≠ 0 := by exact_mod_cast hC
    have halg : IsAlgebraic ℚ (s / t) := by
      refine ⟨Polynomial.C C * Polynomial.X ^ 2 + Polynomial.C A, ?_, ?_⟩
      · intro hz
        have := congrArg (fun p => Polynomial.coeff p 2) hz
        simp at this
        exact hC this
      · have hsq : ((s / t) ^ 2) * (C : ℂ) + (A : ℂ) = 0 := by
          field_simp
          linear_combination h0
        simpa [Polynomial.aeval_def] using by linear_combination hsq
    obtain ⟨r, hr⟩ := hGS halg
    have hst : s = (r : ℂ) * t := by field_simp at hr; linear_combination hr
    have hz : (r : ℝ) * t.re = 0 := by
      have := congrArg Complex.re hst
      simpa [Complex.mul_re, htR, hsI] using this.symm
    rcases mul_eq_zero.1 hz with hz' | hz'
    · exact hs (by rw [hst]; norm_cast; rw [show r = 0 by exact_mod_cast hz']; simp)
    · exact htre hz'
  refine ⟨?_, hB, ?_⟩ <;> by_contra hCz
  · refine aux (fun hC0 => hCz ?_)
    subst hC0
    push_cast at hR
    have hA0 : (A : ℝ) * (t.re * t.re) = 0 := by linarith
    have := (mul_eq_zero.1 hA0).resolve_right (mul_ne_zero htre htre)
    exact_mod_cast this
  · exact aux hCz
