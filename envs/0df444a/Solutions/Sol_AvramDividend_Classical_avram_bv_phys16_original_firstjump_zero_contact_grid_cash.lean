-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_phys16_original_firstjump_zero_contact_grid_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T13:32:00.737134+00:00
-- url     : https://prove2.me/submissions/884c9fe5-292d-45ae-97fe-bf4108fd55cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys16_original_firstjump_contact_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hDrift : 0 ≤ X.drift)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (m : ℕ),
      (∀ i, i < m →
        u i ≤ u (i + 1) ∧ u (i + 1) ≤ H ∧
        (u (i + 1) : WithTop ℝ≥0) <
          (⨅ v : ℝ≥0,
            if 0 < v ∧ X.X v ω -
                Function.leftLim (fun z : ℝ≥0 => X.X z ω) v < 0
            then (v : WithTop ℝ≥0) else ⊤) ∧
        (∀ v : ℝ≥0, u i ≤ v → v ≤ u (i + 1) →
          riskProcess X x D v ω -
            (rightLimit D v ω - D v ω) = 0)) →
      ∀ f : ℝ → ℝ≥0∞,
        (∑ i ∈ Finset.range m,
          ∫⁻ r in Ioc (u i : ℝ) (u (i + 1) : ℝ), f r
            ∂(dividendMeasure D ω)) =
        (∑ i ∈ Finset.range m,
          ∫⁻ r in Ioc (u i : ℝ) (u (i + 1) : ℝ), f r
            ∂((ENNReal.ofReal X.drift) • volume)) := by
  filter_upwards [
    avram_bv_phys16_original_firstjump_contact_cash
      X hBV hFinite hDrift x C D hD H hH
  ] with ω hω
  intro u m hu f
  apply Finset.sum_congr rfl
  intro i hi
  rcases hu i (Finset.mem_range.mp hi) with ⟨hui, hiH, hiFirst, hiZero⟩
  exact hω (u i) (u (i + 1)) hui hiH hiFirst hiZero f
