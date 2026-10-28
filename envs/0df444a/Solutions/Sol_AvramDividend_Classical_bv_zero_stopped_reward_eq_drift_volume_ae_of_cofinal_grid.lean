-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:00:02.678002+00:00
-- url     : https://prove2.me/submissions/9b6c3d53-dcdf-4254-ab17-088c1b825183

import Theorems.Thm_AvramDividend_Classical_bv_zero_surviving_stieltjes_countable_grid_ae
import Theorems.Thm_AvramDividend_Classical_zero_stopped_weighted_grid_prefixes_to_paymentTimes
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A cofinal grid upgrades all surviving Stieltjes prefix identities to the
complete stopped payment interval, for every nonnegative reward weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (grid : ℕ → ℝ≥0)
    (hcofinal : ∀ σ : ℝ≥0∞, ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards
    [bv_zero_surviving_stieltjes_countable_grid_ae
      X hStanding hBV hFinite grid] with ω hω
  intro f
  exact zero_stopped_weighted_grid_prefixes_to_paymentTimes
    (barrierRuinTime X 0 ω) grid
    (dividendMeasure (runningSup X) ω)
    ((ENNReal.ofReal X.drift) • volume) f
    (hcofinal (barrierRuinTime X 0 ω))
    (fun n hn => hω n hn f)
    (runningSup_dividendMeasure_zero_initial_atom X 0 le_rfl ω)
    (by simp)
