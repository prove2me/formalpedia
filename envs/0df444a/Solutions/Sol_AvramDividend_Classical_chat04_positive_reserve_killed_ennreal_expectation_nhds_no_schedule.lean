-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_ennreal_expectation_nhds_no_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:30:09.092997+00:00
-- url     : https://prove2.me/submissions/758d0414-0126-4c61-9050-00c3bc22f444

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_scale_real_ennreal_integral_bridge
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Time-zero continuity of the killed scale expectation in ENNReal follows
from its real version and the verified uniform-moment conversion bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x) :
    Filter.Tendsto
      (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by
  let F : ℝ≥0 → ℝ := fun t => ∫ ω,
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P
  let G : ℝ≥0 → ENNReal := fun t => ∫⁻ ω,
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P
  have hReal : Tendsto F (𝓝 0) (𝓝 (W x)) := by
    simpa [F] using
      (chat04_positive_reserve_killed_scale_expectation_nhds_no_schedule
        X q hq W hW θ x hθ hψ hx)
  have hEq : G = fun t => ENNReal.ofReal (F t) := by
    funext t
    exact chat04_history_killed_scale_real_ennreal_integral_bridge
      X q hq W hW θ x hθ hψ t
  change Tendsto G (𝓝 0) (𝓝 (ENNReal.ofReal (W x)))
  rw [hEq]
  exact (ENNReal.continuous_ofReal.tendsto (W x)).comp hReal
