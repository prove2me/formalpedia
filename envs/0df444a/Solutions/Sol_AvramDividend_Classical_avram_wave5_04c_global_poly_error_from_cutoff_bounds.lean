-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_global_poly_error_from_cutoff_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:22:53.857139+00:00
-- url     : https://prove2.me/submissions/66827ec4-cc52-46b2-99d2-6b0debafaabb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Transfer a weighted endpoint polynomial approximation and a controlled
cutoff tail into a global logarithmic jump-size error estimate. -/
theorem solution
    (g : ℝ → ℝ) (G : C(unitInterval.Elem, ℝ)) (Q : Polynomial ℝ)
    (b ε K : ℝ)
    (hQ : ∀ t : unitInterval.Elem,
      |Polynomial.eval (t : ℝ) Q - (1 - (t : ℝ)) * G t| ≤
        ε * (1 - (t : ℝ)))
    (hmatch : ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
      (1 - (t : ℝ)) * G t = g (t : ℝ))
    (hG : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ K * |Real.log (t : ℝ)|)
    (hg : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |g (t : ℝ)| ≤ K * |Real.log (t : ℝ)|) :
    ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q - g (t : ℝ)| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < b then 2 * K * |Real.log (t : ℝ)| else 0) := by
  intro t ht
  by_cases htb : (t : ℝ) < b
  · have htri :
        |Polynomial.eval (t : ℝ) Q - g (t : ℝ)| ≤
          |Polynomial.eval (t : ℝ) Q - (1 - (t : ℝ)) * G t| +
          |(1 - (t : ℝ)) * G t - g (t : ℝ)| := by
      convert abs_sub_le (Polynomial.eval (t : ℝ) Q)
        ((1 - (t : ℝ)) * G t) (g (t : ℝ)) using 1
    have htri2 :
        |(1 - (t : ℝ)) * G t - g (t : ℝ)| ≤
          |(1 - (t : ℝ)) * G t| + |g (t : ℝ)| :=
      by simpa using (abs_sub_le ((1 - (t : ℝ)) * G t) (0 : ℝ) (g (t : ℝ)))
    calc
      |Polynomial.eval (t : ℝ) Q - g (t : ℝ)| ≤
          |Polynomial.eval (t : ℝ) Q - (1 - (t : ℝ)) * G t| +
            |(1 - (t : ℝ)) * G t - g (t : ℝ)| := htri
      _ ≤ ε * (1 - (t : ℝ)) +
          (K * |Real.log (t : ℝ)| + K * |Real.log (t : ℝ)|) :=
        add_le_add (hQ t) (htri2.trans (add_le_add (hG t ht) (hg t ht)))
      _ = ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < b then 2 * K * |Real.log (t : ℝ)| else 0) := by
        simp [htb]
        ring
  · have hb : b ≤ (t : ℝ) := le_of_not_gt htb
    have hqt := hQ t
    rw [hmatch t hb] at hqt
    simpa [htb] using hqt
