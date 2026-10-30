-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:53:57.864543+00:00
-- url     : https://prove2.me/submissions/bc4eb4cc-3849-43db-b786-7fbd3c97bd35

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_levy_capped_two_sided_first_exit_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Actual upper-first BV grid histories remain alive at their sampled stopping clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (a x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < -x ∨ a-x < X.X t ω} τ)
    (hτUp : (τ : ℝ≥0∞) = twoSidedExitUpTime X (a-x) ω)
    (hup : twoSidedExitUpTime X (a-x) ω <
      twoSidedExitDownTime X (-x) ω)
    (hbefore : τ < T)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    ∀ᶠ n in atTop,
      ∀ s : ℝ≥0, s ≤ min ((K n ω : ℝ≥0) * mesh n) T →
        0 ≤ x + X.X s ω := by
  have hε : 0 < T - τ := tsub_pos_of_lt hbefore
  have hsum : τ + (T - τ) = T := by
    simpa only [add_comm] using
      (tsub_add_cancel_of_le (le_of_lt hbefore))
  have hcap : ∀ᶠ n in atTop,
      τ + (T - τ) ≤ (Nat.ceil (T / mesh n) : ℝ≥0) * mesh n := by
    filter_upwards with n
    simpa only [hsum] using
      (chat03_nnreal_grid_ceiling_bracket T (mesh n) (hpos n)).1
  have hfirst := chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
    X ω (-x) (a-x) τ (T-τ) hτ hε mesh hmesh hpos
      (fun n => Nat.ceil (T / mesh n)) hcap K hK
  have hclock := levy_capped_two_sided_first_exit_clock_tendsto
    X ω (-x) (a-x) τ T hτ mesh hmesh hpos
      (fun n => K n ω) hfirst
  have hclock' : Tendsto
      (fun n => min ((K n ω : ℝ≥0) * mesh n) T)
      atTop (𝓝 τ) := by
    simpa only [min_eq_left hbefore.le] using hclock
  have hgap : (τ : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω := by
    simpa only [hτUp] using hup
  exact avram_ws01b_lower_clock_eventually_closed_survival_of_mesh_tendsto
    X x ω τ (fun n => min ((K n ω : ℝ≥0) * mesh n) T)
    hclock' hgap
