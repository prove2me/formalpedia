-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_stopped_reward_eq_drift_volume_ae_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:07:29.631871+00:00
-- url     : https://prove2.me/submissions/e1b33b63-9a2a-4cf5-a5c4-fc86bc0b49c7

import Theorems.Thm_AvramDividend_Classical_bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
import Theorems.Thm_AvramDividend_Classical_countable_nnreal_dense_grid_strictly_cofinal
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Bases

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A dense countable deterministic grid exists and yields the full stopped
dividend Stieltjes identity on a common almost-sure event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hStanding : X.Standing)
    (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ f : ℝ → ℝ≥0∞,
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ t in paymentTimes (barrierRuinTime X 0 ω), f t
        ∂((ENNReal.ofReal X.drift) • volume)) := by
  obtain ⟨grid, hDense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hcofinal : ∀ σ : ℝ≥0∞, ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ := by
    intro σ t ht htσ
    let u : ℝ≥0 := ⟨t, le_of_lt ht⟩
    have huEq : ENNReal.ofReal t = (u : ℝ≥0∞) := by
      calc
        ENNReal.ofReal t = ENNReal.ofReal (u : ℝ) := by rfl
        _ = (u : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
    have huσ : (u : ℝ≥0∞) < σ := by
      simpa only [huEq] using htσ
    obtain ⟨n, hun, hnσ⟩ :=
      countable_nnreal_dense_grid_strictly_cofinal grid hDense σ u huσ
    refine ⟨n, ?_, hnσ⟩
    change (u : ℝ) ≤ (grid n : ℝ)
    exact_mod_cast (le_of_lt hun)
  exact bv_zero_stopped_reward_eq_drift_volume_ae_of_cofinal_grid
    X hStanding hBV hFinite grid hcofinal
