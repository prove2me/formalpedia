-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:53:30.684934+00:00
-- url     : https://prove2.me/submissions/69b57a2e-3dc3-421f-b384-30a25c865354

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_eq_ruinTime_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine unbounded-variation zero-capped controls pay zero total
discounted Stieltjes dividends at every deterministic horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X 0 0 D)
    (q : ℝ) (T : ℝ≥0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by
  have hident : barrierStrategy X 0 0 = runningSup X := by
    funext t ω
    exact barrierStrategy_self_eq_runningSup X 0 ω t
  have hNear := ae_negative_near_zero_of_unbounded_variation X hBV
  have hRuin : ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by
    filter_upwards [hNear] with ω hNeg
    have hBar0 : barrierRuinTime X 0 ω = 0 :=
      barrierRuinTime_zero_of_near_zero_negative_path X ω hNeg
    have hBarD0 : ruinTime X 0 (barrierStrategy X 0 0) ω = 0 := by
      rw [hident]
      exact (congrFun (barrierRuinTime_eq_ruinTime_runningSup X 0) ω).symm.trans hBar0
    have hLe := zero_cap_ruinTime_le_barrier_ruinTime X D hD ω
    exact bot_unique (hLe.trans (le_of_eq hBarD0))
  have hzero : (fun ω => ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =ᵐ[P]
      (fun _ => (0 : ℝ≥0∞)) := by
    filter_upwards [hRuin] with ω hr
    have hBudget := avram_wave3_03_bv_instant_ruin_closed_horizon_initial_budget
      X 0 0 (by simp) D hD q T ω hr
    exact bot_unique (by simpa using hBudget)
  rw [lintegral_congr_ae hzero]
  simp
