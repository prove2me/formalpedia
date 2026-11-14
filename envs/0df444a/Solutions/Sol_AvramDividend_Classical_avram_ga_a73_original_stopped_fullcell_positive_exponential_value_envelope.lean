-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a73_original_stopped_fullcell_positive_exponential_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:23.026769+00:00
-- url     : https://prove2.me/submissions/75431fc6-5305-4f2e-8ca3-131440511a6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a46_original_safe_cell_spatial_positive_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On every original physical Gaussian full cell strictly before the true stop, the spatial HJB value has one uniform positive-halfline exponential upper envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0,
        s < t → 0 < t → t < ρ ω →
        w (x + X.X t ω - rightLimit D s ω) ≤
          K * Real.exp (θ * (x + X.X t ω - rightLimit D s ω)) := by
  have hu : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  obtain ⟨θ,K,hθ,hK,hUpper⟩ :=
    avram_gledger65_original_topcap_HJB_positive_halfline_exponential_upper
      X hν hσ q hq w C hTopCap hw_smooth hw_gen
      (1 / ((j : ℝ) + 1)) hu
  have hPositive :=
    avram_ga_a46_original_safe_cell_spatial_positive_floor
      X x D hD ρ j hprefix
  refine ⟨θ,K,hθ,hK,?_⟩
  filter_upwards [hPositive] with ω hω
  intro s t hst ht htρ
  exact hUpper _ (hω s t hst ht htρ)
