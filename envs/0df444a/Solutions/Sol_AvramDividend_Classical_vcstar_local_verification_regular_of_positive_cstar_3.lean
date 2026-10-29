-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:15:39.812854+00:00
-- url     : https://prove2.me/submissions/3eccaafe-7316-48e1-b75f-d55ed2e69585

import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_global_smooth_of_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Restrict global positive-half-line smoothness to the continuation region,
combining it with the established zero-boundary regularity conditions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation →
          ContDiffOn ℝ 2 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
       (X.BoundedVariation →
          ContDiffOn ℝ 1 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W})) := by
  obtain ⟨hcontinuous, hnonneg, hnegative⟩ :=
    vcstar_basic_boundary_regular_of_positive_cstar X hX q hq W hW hc hcpos
  obtain ⟨hglobal2, hglobal1⟩ :=
    vcstar_global_smooth_of_positive_cstar X hX q hq W hW hc hcpos h_smooth
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W} ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  refine ⟨hcontinuous, hnonneg, hnegative, ?_, ?_⟩
  · intro hnbv
    exact (hglobal2 hnbv).mono hsubset
  · intro hbv
    exact (hglobal1 hbv).mono hsubset
