-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_capped_finset_dividendMeasure_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:32:04.797981+00:00
-- url     : https://prove2.me/submissions/7d8725e8-522b-47df-aba0-69f3ff5847fc

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
    (ω : Ω) (S : Finset ℝ)
    (hNonneg : ∀ s ∈ S, 0 ≤ s)
    (hActive : ∀ s ∈ S,
      s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in (S : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
    ∑ s ∈ S, ENNReal.ofReal (Real.exp (-(q * s)) *
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))) := by
  rw [lintegral_finset]
  refine Finset.sum_le_sum ?_
  intro s hs
  have hEq : (s.toNNReal : ℝ) = s :=
    Real.coe_toNNReal s (hNonneg s hs)
  have hBound := local_verification_capped_dividendMeasure_atom_bound
    X x q w C hw_cont hw_smooth hw_hjb
    D hD hxC ω s.toNNReal (hActive s hs)
  simpa only [hEq] using hBound
