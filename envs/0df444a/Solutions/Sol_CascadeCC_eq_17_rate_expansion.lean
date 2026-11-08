-- Prove2me | solution 1 for CascadeCC.eq_17_rate_expansion
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-07T14:55:59.40076+00:00
-- url     : https://prove2.me/submissions/f7639f10-82e1-48cf-9ffc-327011014ba1

import Mathlib

/-- CascadeCC eq. (17): expansion of the corrected rate around `a = v / σ`. -/
theorem solution (v σ a δv δσ : ℝ) (hσ : σ ≠ 0) (hσ' : σ + δσ ≠ 0)
    (hv : v = σ * a) :
    (v - δv) / (σ + δσ) = a + (-(δv / σ) - (v - δv) * δσ / (σ * (σ + δσ))) ∧
      (v - δv) / (σ + δσ) =
        a - δv / σ - v * δσ / σ ^ 2 + δv * δσ / σ ^ 2 +
          (v - δv) * δσ ^ 2 / (σ ^ 2 * (σ + δσ)) := by
  subst hv
  constructor <;> field_simp <;> ring
