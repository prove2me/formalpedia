-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_l1_global_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:56:42.10251+00:00
-- url     : https://prove2.me/submissions/ec021471-889d-478c-91f2-408d9695341f

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Positive-time L1 and causal support imply global real-line L1. -/
theorem solution
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0) :
    Integrable f volume := by
  have hs : Function.support f ⊆ Ioi (0 : ℝ) := by
    intro x hx
    by_contra hnot
    exact hx (hzero x (le_of_not_gt hnot))
  exact (integrableOn_iff_integrable_of_support_subset hs).mp hf
