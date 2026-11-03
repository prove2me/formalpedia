-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_canonical_hjump_of_C1_and_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:20:42.725886+00:00
-- url     : https://prove2.me/submissions/b605dcec-5d3f-433a-a6c1-4bb0b1f3de23

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact canonical BV hjump hypothesis follows from strict-interior HJB gradient, closed-cap continuity and the true admissibility inequalities. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
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
  exact
    avram_wave7_02_original_BV_controlled_closed_cap_right_dividend_jump_C1_envelope
      X hX C hC w hw_cont hw_smooth hw_grad
      x hx D hD ω t hPost hDiv hCap

