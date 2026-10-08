-- Prove2me | solution 1 for AvramDividend.Classical.excursion_inverse_laplace_lower_bound_excludes_exponential_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:19:14.596192+00:00
-- url     : https://prove2.me/submissions/06d2d34f-f6fa-45c6-b8a4-96b7fb2e4525

import Mathlib
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_exponential_beats_inverse

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical

theorem solution
    (c C x : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hx : 0 < x)
    (henvelope : ∀ θ : ℝ, 0 < θ →
      c / θ ≤ C * Real.exp (-(θ * x))) : False := by
  have hCpos : 0 < C + 1 := by linarith
  obtain ⟨θ, hθ, hsmall⟩ :=
    excursion_laplace_exponential_beats_inverse (c / (C + 1)) x
      (div_pos hc hCpos) hx
  have hlower : c ≤ (C * Real.exp (-(θ * x))) * θ :=
    (div_le_iff₀ hθ).mp (henvelope θ hθ)
  have hnonneg : 0 ≤ θ * Real.exp (-(θ * x)) :=
    (mul_pos hθ (Real.exp_pos _)).le
  have hupper :
      C * (θ * Real.exp (-(θ * x))) ≤
        (C + 1) * (θ * Real.exp (-(θ * x))) :=
    mul_le_mul_of_nonneg_right (by linarith) hnonneg
  have hstrict :
      (C + 1) * (θ * Real.exp (-(θ * x))) < c := by
    have htmp := (lt_div_iff₀ hCpos).mp hsmall
    nlinarith
  nlinarith [hlower, hupper, hstrict]
