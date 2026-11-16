-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:58:21.844002+00:00
-- url     : https://prove2.me/submissions/5c61c575-53b1-43c7-a7bf-efb2efea1e86

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hd : X.drift = 1)
    (hPath : ∀ s : ℝ≥0, s ≤ T →
      X.X s ω = (s : ℝ) * X.drift) :
    (dividendMeasure (barrierStrategy X 0 0) ω)
      (Ioc (0 : ℝ) (t : ℝ)) = ENNReal.ofReal (t : ℝ) := by
  have hnonneg : 0 ≤ X.drift := by rw [hd]; norm_num
  have hD :=
    avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
      X ω T hnonneg (by
        intro s hs
        rw [hPath s hs]
        ring)
  have hRunning : ∀ u : ℝ, 0 ≤ u → u ≤ (T : ℝ) →
      runningSup X u.toNNReal ω = X.drift * u := by
    intro u hu huT
    have htime : u.toNNReal ≤ T := by
      exact_mod_cast (show (u.toNNReal : ℝ) ≤ (T : ℝ) by
        simpa [Real.coe_toNNReal, max_eq_left hu] using huT)
    have hvalue := (hD u.toNNReal htime).1
    rw [barrierStrategy_self_eq_runningSup] at hvalue
    simpa [Real.coe_toNNReal, max_eq_left hu] using hvalue
  have hMass :=
    runningSup_dividendMeasure_Ioc_eq_drift_before_time
      X ω (T : ℝ) 0 (t : ℝ) hRunning
        (by norm_num) (by positivity)
        (by exact_mod_cast ht)
  have hDef : barrierStrategy X 0 0 = runningSup X := by
    funext s v
    exact barrierStrategy_self_eq_runningSup X 0 v s
  rw [hDef]
  rw [hd] at hMass
  simpa only [one_mul, sub_zero] using hMass
