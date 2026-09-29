-- Prove2me | solution 1 for DiazModulus.logAlg_conj_stable
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T06:57:34.739573+00:00
-- url     : https://prove2.me/submissions/34218734-77e1-4ae6-b75b-00db05d8e138

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-- Algebraicity over `ℚ` survives complex conjugation: a rational polynomial killing `z`
has coefficients fixed by `conj`, so it kills `conj z` too. -/
private theorem isAlgebraic_conj {z : ℂ} (h : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hpz⟩ := h
  refine ⟨p, hp0, ?_⟩
  have hc := congrArg (starRingEnd ℂ) hpz
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, map_sum, Polynomial.sum]
    using hc

open DiazModulus in
theorem solution (u : ℂ) (h : u ∈ LogAlg) : conj u ∈ LogAlg := by
  show IsAlgebraic ℚ (Complex.exp (conj u))
  rw [Complex.exp_conj]
  exact isAlgebraic_conj h
