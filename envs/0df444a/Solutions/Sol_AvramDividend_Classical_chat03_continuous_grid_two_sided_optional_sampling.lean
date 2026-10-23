-- Prove2me | solution 1 for AvramDividend.Classical.chat03_continuous_grid_two_sided_optional_sampling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T10:31:36.337262+00:00
-- url     : https://prove2.me/submissions/79184527-982a-4c2a-92e2-34119c74e010

import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_martingale_monotone_clock_reindex_exists
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-!
Bounded first-exit optional sampling commutes with deterministic monotone
reindexing of any continuous-time adapted process and martingale.
This applies to genuinely killed scale martingales when available.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Z M : ℝ≥0 → Ω → ℝ)
    (hZ : Adapted 𝓕 Z) (hM : Martingale M 𝓕 P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω, M (clock (hittingBtwn
      (fun k ω => max (Z (clock k) ω - upper)
        (lower - Z (clock k) ω))
      (Set.Ioi (0 : ℝ)) 0 m ω)) ω ∂P) =
    ∫ ω, M (clock 0) ω ∂P := by
  obtain ⟨H, hH, hMG⟩ :=
    chat03_martingale_monotone_clock_reindex_exists M hM clock hc
  have hZG : Adapted H (fun k ω => Z (clock k) ω) := by
    intro k
    rw [hH k]
    exact hZ (clock k)
  exact chat03_two_sided_grid_stopped_martingale_identity
    (fun k ω => Z (clock k) ω)
    (fun k ω => M (clock k) ω)
    hZG hMG lower upper m
