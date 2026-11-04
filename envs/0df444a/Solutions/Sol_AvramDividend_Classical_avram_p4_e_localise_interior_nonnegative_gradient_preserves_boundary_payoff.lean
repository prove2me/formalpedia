-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_interior_nonnegative_gradient_preserves_boundary_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:02:22.050417+00:00
-- url     : https://prove2.me/submissions/565d576e-7309-4134-80f8-5c41376340d5

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Interior derivative sign and boundary continuity preserve nonnegative payoff. -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 ≤ y)
    (hw0 : 0 ≤ w 0)
    (hcont : ContinuousOn w (Icc 0 y))
    (hdiff : DifferentiableOn ℝ w (Ioo 0 y))
    (hgrad : ∀ z ∈ Ioo 0 y, 0 ≤ deriv w z) :
    0 ≤ w y := by
  have hmono : MonotoneOn w (Icc 0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hcont
    · simpa only [interior_Icc] using hdiff
    · simpa only [interior_Icc] using hgrad
  exact le_trans hw0 (hmono ⟨le_rfl, hy⟩ ⟨hy, le_rfl⟩ hy)
