-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:13:02.387125+00:00
-- url     : https://prove2.me/submissions/d258a004-c25b-48a8-9c86-f29c6876b41f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

/-! The original full real-clock stopped payoff with strictly pre-ruin
paymentTimes is bounded at q=ψ(1); no Stieltjes atom is dropped. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
        ∂dividendMeasure D ω ∂P) ≤ ENNReal.ofReal (Real.exp x) := by
  classical
  have hpath (ω : Ω) :
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
        ∂dividendMeasure D ω) =
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        else 0 ∂dividendMeasure D ω) := by
    let τ := ruinTime X x D ω
    have hE : MeasurableSet (paymentTimes τ ∩ Iic (T : ℝ)) :=
      (paymentTimes_measurable τ).inter measurableSet_Iic
    calc
      (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
        ∂dividendMeasure D ω) =
      (∫⁻ s in paymentTimes τ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        ∂dividendMeasure D ω) := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem hE] with s hs
          have h0 : 0 ≤ s := by
            have hp := hs.1
            change s ∈ Ici (0 : ℝ) ∩
              ({0} ∪ {t : ℝ | ENNReal.ofReal t < τ}) at hp
            exact hp.1
          rw [Real.coe_toNNReal s h0]
      _ = (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        ∂(dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) :=
          avram_wave4_04b_stopped_original_reward_eq_closed_horizon_restriction
            D hD.1.1 ω T τ _
      _ = (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        if s ∈ paymentTimes τ then
          ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        else 0 ∂dividendMeasure D ω) := by
          rw [← lintegral_indicator (paymentTimes_measurable τ)]
          rfl
  calc
    _ = (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        if s ∈ paymentTimes (ruinTime X x D ω) then
          ENNReal.ofReal (Real.exp (-(X.ψ 1 * (s.toNNReal : ℝ))))
        else 0 ∂dividendMeasure D ω ∂P) := by
      apply lintegral_congr_ae
      filter_upwards [] with ω
      exact hpath ω
    _ ≤ ENNReal.ofReal (Real.exp x) :=
      avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_exponential_verification
        X x C D hD T hT
