-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_original_BV_countable_local_C1_postpayment_composition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:01:52.55941+00:00
-- url     : https://prove2.me/submissions/0d49d550-f08b-4e88-8852-5615caa66276

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat07b_original_BV_local_C1_postpayment_composition
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- One a.s. event controls all countably localised source-specific BV C1 postpayment compositions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (cap : ℝ)
    (lo hi : ℕ → ℝ)
    (hBand : ∀ n, lo n < hi n)
    (hInside : ∀ n, Icc (lo n) (hi n) ⊆ Ioo 0 cap)
    (hwC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ T : ℝ≥0,
      (∀ t : ℝ≥0,
        x + X.X (min t T) ω - rightLimit D (min t T) ω ∈
          Icc (lo n) (hi n)) →
      BoundedVariationOn
        (fun t : ℝ≥0 =>
          w (x + X.X (min t T) ω - rightLimit D (min t T) ω))
        Set.univ := by
  apply (MeasureTheory.ae_all_iff).2
  intro n
  exact avram_chat07b_original_BV_local_C1_postpayment_composition
    X hX hBV x D hD w cap (lo n) (hi n)
    (hBand n) (hInside n) hwC1
