-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_actual_upper_killed_reward_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:38:34.989856+00:00
-- url     : https://prove2.me/submissions/807822c5-9d7c-485d-936e-55d7cbc454ec

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_upper_exit_grid_history_eventually
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_actual_upper_terminal_positive_window

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The true upper-first stopped-grid killed reward eventually agrees
with the unrestricted q-scale reward, then inherits its pathwise limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (x : ℝ) (τ : ℝ≥0) (t : ℕ → ℝ≥0)
    (ht : Tendsto t atTop (nhds τ))
    (hBefore : ∀ s : ℝ≥0, s ≤ τ → 0 ≤ x + X.X s ω)
    (hcont : ContinuousWithinAt (fun s : ℝ≥0 => X.X s ω) (Set.Ici τ) τ)
    (hpositive : 0 < x + X.X τ ω)
    (q : ℝ) (W : ℝ → ℝ) (y : ℝ)
    (hRaw : Tendsto (fun n =>
      Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω))
      atTop (nhds y)) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}).indicator
        (fun η => Real.exp (-(q * (t n : ℝ))) *
          W (x + X.X (t n) η)) ω) atTop (nhds y) := by
  let R : ℕ → Ω → ℝ := fun n η =>
    Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) η)
  let B : ℕ → Set Ω := fun n => {η : Ω |
    ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s η}
  have hAfter :=
    avram_root29_01_actual_upper_terminal_positive_window
      X ω x τ hcont hpositive
  have hSurv :=
    avram_root29_01_upper_exit_grid_history_eventually
      X ω x τ t ht hBefore hAfter
  have hEq : (fun n => R n ω) =ᶠ[atTop]
      (fun n => (B n).indicator (R n) ω) := by
    filter_upwards [hSurv] with n hn
    exact (Set.indicator_of_mem (show ω ∈ B n from hn) (R n)).symm
  have hRaw' : Tendsto (fun n => R n ω) atTop (nhds y) := by
    simpa only [R] using hRaw
  simpa only [R, B] using hRaw'.congr' hEq
