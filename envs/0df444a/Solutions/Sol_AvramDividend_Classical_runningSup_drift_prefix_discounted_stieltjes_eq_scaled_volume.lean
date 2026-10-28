-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:54:41.226982+00:00
-- url     : https://prove2.me/submissions/cb09db73-dea1-4e0f-b3b0-fa89e362b8c5

import Theorems.Thm_AvramDividend_Classical_measure_restrict_Ioc_eq_of_local_Ioc_agreement
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ)
    (hT : 0 ≤ T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u)
    (hDrift : 0 ≤ X.drift)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂((ENNReal.ofReal X.drift) • volume)) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let ν : Measure ℝ := (ENNReal.ofReal X.drift) • volume
  have hFinite : μ (Ioc (0 : ℝ) T) < ⊤ := by
    change (dividendMeasure (runningSup X) ω) (Ioc (0 : ℝ) T) < ⊤
    rw [runningSup_dividendMeasure_Ioc_eq_drift_before_time
      X ω T 0 T hPath le_rfl hT le_rfl]
    exact ENNReal.ofReal_lt_top
  have hMass (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
      μ (Ioc s t) = ν (Ioc s t) := by
    change (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ((ENNReal.ofReal X.drift) • volume) (Ioc s t)
    rw [runningSup_dividendMeasure_Ioc_eq_drift_before_time
      X ω T s t hPath hs hst ht]
    simpa [Measure.smul_apply, Real.volume_Ioc, smul_eq_mul] using
      (ENNReal.ofReal_mul hDrift :
        ENNReal.ofReal (X.drift * (t - s)) =
          ENNReal.ofReal X.drift * ENNReal.ofReal (t - s))
  have heq : μ.restrict (Ioc (0 : ℝ) T) =
      ν.restrict (Ioc (0 : ℝ) T) :=
    measure_restrict_Ioc_eq_of_local_Ioc_agreement μ ν T hT hFinite hMass
  exact congrArg (fun m : Measure ℝ => ∫⁻ t, f t ∂m) heq
