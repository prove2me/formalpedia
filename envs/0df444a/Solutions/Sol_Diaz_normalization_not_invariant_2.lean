-- Prove2me | solution 2 for Diaz.normalization_not_invariant
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:34:24.159354+00:00
-- url     : https://prove2.me/submissions/38ec15a7-b0e6-4c7d-991b-300159263bc6

/-
`Diaz.normalization_not_invariant`, with `HL` no longer used.

The witness is unchanged: `u = 2πi`, for which `exp u = 1` is algebraic while
`u/‖u‖ = i`. What changes is how `exp i` is shown transcendental. The node takes
Hermite–Lindemann as an explicit hypothesis `HL`; but the mission already owns
its contrapositive unconditionally, as the published node
`Diaz.transcendental_of_candidate` — if `z ≠ 0` and `exp z` is algebraic then `z`
is transcendental. Applied to `z = i`, which is non-zero and algebraic, it gives
`exp i` transcendental directly.

## Flagging a redundant hypothesis

`HL` is therefore **not load-bearing**: the statement holds unconditionally in
this environment, and a reader should not take the hypothesis as recording a
genuine assumption. It is kept because the node's statement may not be weakened,
and the proof below simply does not use it. This is worth recording on the node:
it is the difference between "the mission needs Hermite–Lindemann here" and "the
mission already has it".
-/
import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_transcendental_of_candidate

open ComplexConjugate
open Diaz

open Diaz in
theorem solution
    (HL : ∀ z : ℂ, z ≠ 0 → IsAlgebraic ℚ z → Transcendental ℚ (Complex.exp z)) :
    ∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ (Complex.exp u) ∧
      Transcendental ℚ (Complex.exp ((((‖u‖ : ℝ) : ℂ))⁻¹ * u)) := by
  have hI : IsAlgebraic ℚ Complex.I := by
    refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
    · intro h
      have := congrArg (Polynomial.coeff · 0) h
      simp at this
    · simp [Polynomial.aeval_def, Complex.I_sq]
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨2 * (Real.pi : ℂ) * Complex.I, ?_, ?_, ?_⟩
  · simp [Complex.I_ne_zero, Real.pi_ne_zero]
  · rw [Complex.exp_two_pi_mul_I]; exact isAlgebraic_one
  · have hnorm : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [hnorm]
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpi
    have e : (((2 * Real.pi : ℝ) : ℂ))⁻¹ * (2 * (Real.pi : ℂ) * Complex.I) = Complex.I := by
      push_cast
      field_simp
    rw [e]
    -- `exp i` is transcendental: otherwise `i` would be, and it is not.
    intro halg
    exact Diaz.transcendental_of_candidate Complex.I_ne_zero halg hI
