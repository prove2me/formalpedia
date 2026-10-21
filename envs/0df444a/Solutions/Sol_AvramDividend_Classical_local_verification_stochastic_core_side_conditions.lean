-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_stochastic_core_side_conditions
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:56:49.128982+00:00
-- url     : https://prove2.me/submissions/d655f586-5b84-4f96-90ed-536a79dfb531

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_capped_admissible_bookReserve_candidate_nonnegative_preRuin
import Theorems.Thm_AvramDividend_Classical_capped_admissible_hjb_right_dividend_atom_control

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy hyC
    have h :=
      local_verification_hjb_implies_components
        X q w C hw_hjb y hy hyC
    exact ⟨h.1, h.2.1⟩
  · intro y hy hyC
    exact (local_verification_hjb_implies_components
      X q w C hw_hjb y hy hyC).2.2
  · exact capped_admissible_bookReserve_candidate_nonnegative_preRuin
      X q w C hw_cont hw0 hw_smooth hw_hjb x D hD
  · exact capped_admissible_hjb_right_dividend_atom_control
      X q w C hw_cont hw_smooth hw_hjb x hxc D hD
