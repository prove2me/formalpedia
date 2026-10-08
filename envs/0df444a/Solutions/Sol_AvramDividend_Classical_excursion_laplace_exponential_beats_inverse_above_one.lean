-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_exponential_beats_inverse_above_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:32:48.264274+00:00
-- url     : https://prove2.me/submissions/1895a25e-bf21-4b28-b018-56bd2f2b5978

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Topology

theorem solution (r x : ℝ) (hr : 0 < r) (hx : 0 < x) :
    ∃ θ : ℝ, 1 ≤ θ ∧ θ * Real.exp (-(θ * x)) < r := by
  have hlimit :
      Tendsto (fun t : ℝ => t ^ (1 : ℕ) * Real.exp (-t))
        atTop (nhds (0 : ℝ)) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hsmall : ∀ᶠ t : ℝ in atTop,
      t ^ (1 : ℕ) * Real.exp (-t) < r * x :=
    hlimit.eventually (eventually_lt_nhds (mul_pos hr hx))
  have hbig : ∀ᶠ t : ℝ in atTop, x < t :=
    eventually_gt_atTop x
  obtain ⟨t, ht, hlt⟩ := (hbig.and hsmall).exists
  have ht0 : 0 < t := lt_trans hx ht
  refine ⟨t / x, ?_, ?_⟩
  · exact (le_div_iff₀ hx).2 (by linarith)
  · have hscale : -(t / x * x) = -t := by
      field_simp
    rw [hscale]
    have hrewrite : t / x * Real.exp (-t) =
        (t * Real.exp (-t)) / x := by ring
    rw [hrewrite]
    apply (div_lt_iff₀ hx).2
    simpa only [pow_one] using hlt
