-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_04_original_BV_strict_survival_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:56:13.473875+00:00
-- url     : https://prove2.me/submissions/4c915682-bf47-49b6-866a-4a6f9dd0208c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_nonnegative_strictly_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (S : ℝ≥0) :
    Integrable (fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0) P := by
  classical
  have hInitial : ∀ ω, 0 ≤ rightLimit D 0 ω := by
    intro ω
    change 0 ≤ ⨅ (s : Ioi (0 : ℝ≥0)), D s ω
    apply le_ciInf
    intro s
    calc
      0 = D 0 ω := (hD.1 ω).symm
      _ ≤ D s ω := hD.2.1 ω (le_of_lt s.property)
  have hXJoint : Measurable
      (fun p : ℝ≥0 × Ω => X.X p.1 p.2) :=
    chat04_levy_joint_time_state_measurable X
  have hXT : Measurable (fun ω : Ω => X.X S ω) :=
    hXJoint.comp (measurable_const.prodMk measurable_id)
  have hPostMeas : Measurable (fun ω =>
      x + X.X S ω - rightLimit D S ω) :=
    (measurable_const.add hXT).sub
      (dividendStrategy_rightLimit_measurable D hD S)
  have hSurvivalMeas : MeasurableSet
      {ω | (S : ℝ≥0∞) < ruinTime X x D ω} :=
    measurableSet_lt measurable_const (ruinTime_measurable X x D hD)
  have hSurvivalNonneg : ∀ᵐ ω ∂P,
      (S : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ x + X.X S ω - rightLimit D S ω :=
    Filter.Eventually.of_forall (fun ω hs =>
      postPaymentReserve_nonnegative_strictly_before_ruin
        X x D hD ω S hs)
  exact avram_wave8_04_original_BV_survival_terminal_integrable_of_source_bounds
    X hBV q w hw_cont hw_neg x D hD hInitial S
    hPostMeas hSurvivalMeas hSurvivalNonneg
