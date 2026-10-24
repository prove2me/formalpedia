-- Prove2me | solution 1 for AvramDividend.Classical.causal_antitone_reversed_kernel_cutoff_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:18:27.220536+00:00
-- url     : https://prove2.me/submissions/2df35689-2262-4c2d-bc9f-8b84a04292ec

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_antitone_positive_kernel_mass_lower_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Positive-time antitonicity controls the left convolution interval by cutoff mass. -/
theorem solution
    (κ : ℝ → ℝ) (x u ρ : ℝ) (hxu : 0 < x - u)
    (hanti : AntitoneOn κ (Ioi (0 : ℝ)))
    (hint : IntervalIntegrable κ volume 0 (x - u))
    (hmass : (∫ t in (0 : ℝ)..(x - u), κ t) ≤ ρ) :
    ∀ s ∈ Ioo (0 : ℝ) u, κ (x - s) ≤ ρ / (x - u) := by
  have hpoint :=
    AvramDividend.Classical.antitone_positive_kernel_mass_lower_bound
      κ hanti (x - u) hxu hint
  have hcutoff : κ (x - u) ≤ ρ / (x - u) := by
    apply (le_div_iff₀ hxu).2
    nlinarith [hpoint, hmass]
  intro s hs
  have hxs : 0 < x - s := by linarith [hs.2]
  have hle : x - u ≤ x - s := by linarith [hs.2]
  exact (hanti hxu hxs hle).trans hcutoff
