-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_allclock_closed_inclusive_reward_le_strict_prepayment_physical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:56:09.066433+00:00
-- url     : https://prove2.me/submissions/d722466d-9b50-476d-bd89-824dce6dc6f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)))
    (ρ : Ω → ℝ≥0) (G : Ω → ℝ)
    (hGdef : ∀ ω, G ω =
      if ρ ω = 0 then w x else
        Real.exp (-(q * (ρ ω : ℝ))) *
          w (if (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
            else riskProcess X x D (ρ ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal)
    (V : Ω → ℝ)
    (hVdef : ∀ ω, V ω = Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, G ω ≤ V ω := by
  intro ω
  by_cases hzero : ρ ω = 0
  · have hV0 :=
      avram_pj_workerC_original_true_zero_stopped_strictpre_reward_eq_initial_w
        X x C D hD w q ρ V hVdef ω hzero
    have hG0 : G ω = w x := by
      simpa only [hzero, ite_true] using hGdef ω
    exact (hG0.trans hV0.symm).le
  · have hpos : 0 < ρ ω := pos_iff_ne_zero.mpr hzero
    have hBound :=
      avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
        X x C D hD w q hq hjump ρ G hGdef ω hpos
    simpa only [hVdef ω] using hBound
