-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_actual_postright_inclusive_reward_positive_clock_le_strict_physical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:25:45.430373+00:00
-- url     : https://prove2.me/submissions/fc3aa75f-17f7-4951-bc6a-86d1e15ea4bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
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
            ∂(dividendMeasure D ω)).toReal) :
    ∀ ω, 0 < ρ ω →
      G ω ≤ Real.exp (-(q * (ρ ω : ℝ))) *
        w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by
  let F : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) *
      w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
        else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  have hF := avram_b244_original_ruinclipped_positive_stop_inclusive_Iic_cash_terminal_contact_le_strict
    X x C D hD w q hq hjump ρ F (by intro ω; rfl)
  intro ω hpos
  have hEq : G ω = F ω := by
    simp [F, hGdef ω, ne_of_gt hpos]
  rw [hEq]
  exact hF ω hpos

