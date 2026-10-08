-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_countable_dividendMeasure_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T08:12:38.106724+00:00
-- url     : https://prove2.me/submissions/34736a12-6d4b-4302-b82f-5cd58a7d6522

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_capped_dividendMeasure_atom_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (S : Set ℝ) (hCountable : S.Countable)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in S,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑' s : S, ENNReal.ofReal (Real.exp (-(q * (s : ℝ))) *
      (w (riskProcess X x D (s : ℝ).toNNReal ω) -
        w (riskProcess X x D (s : ℝ).toNNReal ω -
          (rightLimit D (s : ℝ).toNNReal ω - D (s : ℝ).toNNReal ω)))) := by
  rw [lintegral_countable _ hCountable]
  refine ENNReal.tsum_le_tsum fun s => ?_
  have hEq : ((s : ℝ).toNNReal : ℝ) = (s : ℝ) :=
    Real.coe_toNNReal s.1 (hNonneg s.1 s.2)
  have hBound := local_verification_capped_dividendMeasure_atom_bound
    X x q w C hw_cont hw_smooth hw_hjb
    D hD hxC ω (s : ℝ).toNNReal (hActive s.1 s.2)
  simpa only [hEq] using hBound
