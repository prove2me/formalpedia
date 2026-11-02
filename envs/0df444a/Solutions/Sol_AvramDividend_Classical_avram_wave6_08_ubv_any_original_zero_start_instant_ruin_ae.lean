-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:57:39.23149+00:00
-- url     : https://prove2.me/submissions/c36efe0b-45b7-431b-b1c7-7a5d77dc32bd

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ruinTime X 0 D ω = 0 := by
  have hpre : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X 0 D ω →
        0 ≤ riskProcess X 0 D s ω := by
    intro ω s hs
    exact riskProcess_nonneg_before_ruin X 0 D ω s hs
  have hmeas : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | (0 : ℝ≥0) ≤ s} := by
    intro s
    simp
  have hstop : IsStoppingTime 𝓕
      (fun _ : Ω => (0 : WithTop ℝ≥0)) := by
    first
    | exact isStoppingTime_const 𝓕 (0 : ℝ≥0)
    | exact isStoppingTime_const (𝓕 := 𝓕) (0 : ℝ≥0)
    | exact isStoppingTime_const
    | change ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        {ω : Ω | (0 : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)}
      intro s
      simp
  have hpositive :=
    avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
      X hBV 0 D hD hpre (fun _ : Ω => 0) hmeas hstop
  filter_upwards [hpositive] with ω hω
  by_contra hne
  have hruin : (0 : ℝ≥0∞) < ruinTime X 0 D ω :=
    (pos_iff_ne_zero).2 hne
  have hpos : 0 < riskProcess X 0 D 0 ω := hω hruin
  have hD0 : D 0 ω = 0 := hD.1 ω
  simp [riskProcess, X.X_zero ω, hD0] at hpos
