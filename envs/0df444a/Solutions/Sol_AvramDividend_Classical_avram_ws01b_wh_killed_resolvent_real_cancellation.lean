-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_wh_killed_resolvent_real_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T08:59:10.003994+00:00
-- url     : https://prove2.me/submissions/4bc13c61-2853-4aff-a71f-f8fab728f546

import Mathlib.Tactic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Algebraic cancellation in the proposed genuine finite-rate
Wiener--Hopf proof of killed q-scale harmonicity.
A is ψ(θ), Φ is Φ(r+q), and r is the Laplace time parameter.
This proves only a real scalar identity, not Wiener--Hopf independence. -/
theorem solution
    (r q Φ θ A : ℝ)
    (hr : 0 < r) (hΦ : 0 < Φ) (hθ : Φ < θ)
    (hA : r + q < A) :
    (((r + q) * (θ - Φ)) / (Φ * (A - (r + q)))) *
      (Φ / (θ - Φ) * (1 / r - 1 / (A - q))) =
      (r + q) / (r * (A - q)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hΦ0 : Φ ≠ 0 := ne_of_gt hΦ
  have hθ0 : θ - Φ ≠ 0 := ne_of_gt (sub_pos.mpr hθ)
  have hA0 : A - (r + q) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hA)
  have hAq : A - q ≠ 0 := by
    have h : 0 < A - q := by linarith
    exact ne_of_gt h
  field_simp
  ring
