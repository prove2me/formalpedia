-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:12:46.989053+00:00
-- url     : https://prove2.me/submissions/8d7fbc46-0649-4191-896b-0f826f7513e8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Original controlled BV right-dividend jumps satisfy the canonical C1 HJB candidate drop, including at cap equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      0 ≤ riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) →
      0 ≤ rightLimit D t ω - D t ω →
      ENNReal.ofReal (riskProcess X x D t ω) ≤ C →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
  intro ω t hPost hDiv hCap
  let y : ℝ := riskProcess X x D t ω -
    (rightLimit D t ω - D t ω)
  let z : ℝ := riskProcess X x D t ω
  have hPos : 0 ≤ y := hPost
  have hDivNZ : 0 ≤ z - y := by
    dsimp [y, z]
    linarith only [hDiv]
  have hyz : y ≤ z := sub_nonneg.mp hDivNZ
  have hz0 : 0 ≤ z := hPos.trans hyz
  have hYMem : y ∈ Icc (0 : ℝ) z := ⟨hPos, hyz⟩
  have hZMem : z ∈ Icc (0 : ℝ) z := ⟨hz0, le_refl _⟩
  have hStep :
      z - y ≤ w z - w y :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad z hz0 hCap
      y hYMem z hZMem hyz
  dsimp [y, z] at hStep
  linarith only [hStep]