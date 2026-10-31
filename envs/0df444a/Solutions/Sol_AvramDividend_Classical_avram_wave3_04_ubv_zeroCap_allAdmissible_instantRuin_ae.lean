-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allAdmissible_instantRuin_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:53:21.039404+00:00
-- url     : https://prove2.me/submissions/c07712ef-4c14-4749-85e7-380668b71ed4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every actual zero-capped admissible dividend strategy on an
unbounded-variation Lévy law ruins immediately almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by
  have hident : barrierStrategy X 0 0 = runningSup X := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  filter_upwards [ae_negative_near_zero_of_unbounded_variation X hBV] with ω hNear
  have hBar0 : barrierRuinTime X 0 ω = 0 :=
    barrierRuinTime_zero_of_near_zero_negative_path X ω hNear
  have hBarD0 : ruinTime X 0 (barrierStrategy X 0 0) ω = 0 := by
    rw [hident]
    exact (congrFun (barrierRuinTime_eq_ruinTime_runningSup X 0) ω).symm.trans hBar0
  have hLe := zero_cap_ruinTime_le_barrier_ruinTime X D hD ω
  exact bot_unique (hLe.trans (le_of_eq hBarD0))
