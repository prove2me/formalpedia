-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:05:53.049458+00:00
-- url     : https://prove2.me/submissions/fb1e5d33-7d50-445f-a440-cf9c398f5eea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical admissibility and the closed-cap C1 secant bound control the
    original right dividend at zero and every strict pre-ruin time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
  intro ω t hActive
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hDle : D t ω ≤ rightLimit D t ω :=
    dividendStrategy_le_rightLimit D hStrat ω t
  have hDiv : 0 ≤ rightLimit D t ω - D t ω :=
    sub_nonneg.mpr hDle
  have hNoOver :
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω :=
    hD.1.2 ω t hActive
  have hPost :
      0 ≤ riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) :=
    sub_nonneg.mpr hNoOver
  have hCap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
    by_cases ht0 : t = 0
    · subst t
      have hDzero : D 0 ω = 0 := hStrat.1 ω
      change ENNReal.ofReal (x + X.X 0 ω - D 0 ω) ≤ C
      rw [X.X_zero ω, hDzero]
      simpa using hxc
    · have htpos : (0 : ℝ≥0) < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm ht0)
      exact hD.2 ω t htpos
  have hBound : 0 ≤ riskProcess X x D t ω := by linarith only [hPost, hDiv]
  have hOrder :
      riskProcess X x D t ω -
        (rightLimit D t ω - D t ω) ≤ riskProcess X x D t ω := by
    linarith only [hDiv]
  have hSec :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad
      (riskProcess X x D t ω) hBound hCap
      (riskProcess X x D t ω - (rightLimit D t ω - D t ω))
      ⟨hPost, hOrder⟩
      (riskProcess X x D t ω) ⟨hBound, le_rfl⟩ hOrder
  linarith only [hSec]
