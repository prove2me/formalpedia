-- Prove2me | solution 1 for AvramDividend.Classical.avram_b236_local_gradient_one_secant_controls_original_continuous_dividend_cash
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:20:10.762476+00:00
-- url     : https://prove2.me/submissions/187560b8-39d3-4727-bc77-b6adda73c439

import Mathlib
open Set Filter Topology MeasureTheory
noncomputable section

theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ r ∈ Ioo a b, DifferentiableAt ℝ w r)
    (hgrad : ∀ r ∈ Ioo a b, 1 ≤ deriv w r) :
    b - a ≤ w b - w a := by
  have hmono : MonotoneOn (fun r => w r - r) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact hcont.sub continuousOn_id
    · rw [interior_Icc]
      intro r hr
      exact ((hdiff r hr).sub differentiableAt_id).differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      have h1 : deriv (fun r => w r - r) r = deriv w r - 1 := by
        exact ((hdiff r hr).hasDerivAt.sub (hasDerivAt_id r)).deriv
      rw [h1]
      linarith [hgrad r hr]
  have := hmono ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  simp only at this
  linarith
