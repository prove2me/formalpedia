-- Prove2me | solution 1 for AvramDividend.Classical.chat03_two_sided_grid_stopped_martingale_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:26:24.75723+00:00
-- url     : https://prove2.me/submissions/136335ae-e0d4-4e98-85ac-2fbdb38c83e5

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-!
Finite-grid stopped-martingale identity at the first strict two-sided exit.
The witness is positive iff the sampled reserve is strictly above upper or
strictly below lower, preserving the published two-sided convention.
The proof does not require usual continuous-time filtration hypotheses.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {G : Filtration ℕ mΩ}
    (Z M : ℕ → Ω → ℝ) (hZ : Adapted G Z)
    (hM : Martingale M G P) (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      M (hittingBtwn
        (fun k ω => max (Z k ω - upper) (lower - Z k ω))
        (Set.Ioi (0 : ℝ)) 0 m ω) ω ∂P) =
    ∫ ω, M 0 ω ∂P := by
  let Y : ℕ → Ω → ℝ :=
    fun k ω => max (Z k ω - upper) (lower - Z k ω)
  have hY : Adapted G Y := by
    intro k
    change Measurable[G k]
      (fun ω => max (Z k ω - upper) (lower - Z k ω))
    exact ((hZ k).sub measurable_const).max
      (measurable_const.sub (hZ k))
  exact AvramDividend.Classical.chat03_bounded_first_crossing_martingale_identity
    Y M hY hM 0 m