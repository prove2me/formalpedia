-- Prove2me | solution 1 for Diaz.salem_quartic_relations_of_logs
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T14:39:11.120965+00:00
-- url     : https://prove2.me/submissions/6ec0a19a-672e-472e-9fc4-0577e3029a65

import Mathlib
import Theorems.Thm_Diaz_salem_quartic_relations
import Theorems.Thm_Schanuel_gelfond_schneider

/-- Gelfond–Schneider discharges the hypothesis `hGS` of `Diaz.salem_quartic_relations` when `t`
and `s` are logarithms of algebraic numbers: if `s / t` were algebraic and irrational, then
`exp s = exp ((s / t) * t)` would be transcendental. -/
theorem solution {t s : ℂ} (ht : t ≠ 0) (hs : s ≠ 0)
    (htR : t.im = 0) (hsI : s.re = 0)
    (het : IsAlgebraic ℚ (Complex.exp t)) (hes : IsAlgebraic ℚ (Complex.exp s))
    {A B C : ℚ} (h : (A : ℂ) * t ^ 2 + (B : ℂ) * (t * s) + (C : ℂ) * s ^ 2 = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  refine Diaz.salem_quartic_relations ht hs htR hsI ?_ h
  intro halg
  by_contra hrat
  simp only [not_exists] at hrat
  have hT := Schanuel.gelfond_schneider (s / t) t halg hrat het ht
  rw [div_mul_cancel₀ s ht] at hT
  exact hT hes

#print axioms solution
