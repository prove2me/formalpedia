-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_admissible_BV_ruin_compact_C1_jump_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:51:11.094877+00:00
-- url     : https://prove2.me/submissions/ae70990c-9b68-4ba6-a1c4-c69b23f53cab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_stopped_compact_previsible
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All local stopped-source and compact C1 hypotheses follow from the
original admissible BV control and a genuinely interior compact band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici 0))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (T : ℝ≥0) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hBand : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    (∀ ω, τ ω ≤ T) ∧
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
    MeasurableSet[𝓕.rightCont.predictable] E ∧
    (∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b) ∧
    (∀ p ∈ E, p.1 ≤ T) ∧
    ∃ L R : ℝ, 0 ≤ L ∧ 0 ≤ R ∧
      (∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
        |w u - w v| ≤ L * |u - v|) ∧
      (∀ v : ℝ, v ≤ b → |w v| ≤ R) := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  have hClock :=
    avram_p3_g_localise_original_ruin_stopped_compact_previsible
      X x D hStrategy T a b
  have hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    have hPos : IsOpen {y : ℝ | 0 < y} := isOpen_Ioi
    have hBelow : IsOpen {y : ℝ | ENNReal.ofReal y < C} :=
      isOpen_Iio.preimage ENNReal.continuous_ofReal
    change IsOpen ({y : ℝ | 0 < y} ∩
      {y : ℝ | ENNReal.ofReal y < C})
    exact hPos.inter hBelow
  obtain ⟨L, R, hL, hR, hLip, hWbound⟩ :=
    avram_p3_g_localise_source_BV_C1_compact_Lipschitz_value_bounds
      X hBV C w hwCont hwNeg hwC1 a b ha hab hOpen hBand
  rcases hClock with ⟨hBound, hStop, hEm, hEregion, hTime⟩
  exact ⟨hBound, hStop, hEm, hEregion, hTime,
    L, R, hL, hR, hLip, hWbound⟩
