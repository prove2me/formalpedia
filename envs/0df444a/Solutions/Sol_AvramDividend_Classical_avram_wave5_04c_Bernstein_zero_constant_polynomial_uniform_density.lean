-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:56:57.141582+00:00
-- url     : https://prove2.me/submissions/591edc8c-179d-4a83-9d93-83be9d32233f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Set
open AvramDividend.Classical

/-! Quantitative zero-constant polynomial density on the unit interval. -/
theorem solution (f : C(unitInterval.Elem, ℝ))
    (h0 : f 0 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      ∀ t : unitInterval.Elem,
        |Polynomial.eval (t : ℝ) p - f t| < ε := by
  have hlim := bernsteinApproximation_uniform f
  have hclose : ∀ᶠ n : ℕ in atTop,
      dist (bernsteinApproximation n f) f < ε :=
    (Metric.tendsto_nhds.mp hlim) ε hε
  obtain ⟨n, hn⟩ := hclose.exists
  obtain ⟨p, hp⟩ :=
    avram_wave5_04c_Bernstein_approximation_has_exact_real_polynomial n f
  refine ⟨p, ?_, ?_⟩
  · have hz := hp (0 : unitInterval.Elem)
    rw [bernsteinApproximation.apply_zero] at hz
    simpa [h0] using hz
  · intro t
    have hb := ContinuousMap.dist_apply_le_dist
      (f := bernsteinApproximation n f) (g := f) t
    rw [← hp t] at hb
    exact lt_of_le_of_lt (by simpa only [Real.dist_eq] using hb) hn
