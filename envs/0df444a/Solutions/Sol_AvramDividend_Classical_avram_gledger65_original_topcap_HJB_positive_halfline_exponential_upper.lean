-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:52:59.552688+00:00
-- url     : https://prove2.me/submissions/297876ce-ae18-4b34-b423-3a95ae323972

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger64_topcap_C2_supplies_original_classical_derivatives
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original zero-jump top-cap HJB assumptions yield exactly the one-sided
    spatial growth envelope used by the stopped physical source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u : ℝ) (hu : 0 < u) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, u ≤ y → w y ≤ K * Real.exp (θ * y) := by
  have hsmooth :=
    avram_gledger64_topcap_C2_supplies_original_classical_derivatives
      w C hTopCap hw_smooth
  have hgen (y : ℝ) (hy : 0 < y) :
      X.generator w y - q * w y ≤ 0 := by
    exact (hw_gen y hy (by simp [hTopCap])).2
  exact avram_gledger61_original_zerojump_HJB_one_sided_exponential_bound
    X hν hσ q hq w hsmooth hgen u hu
