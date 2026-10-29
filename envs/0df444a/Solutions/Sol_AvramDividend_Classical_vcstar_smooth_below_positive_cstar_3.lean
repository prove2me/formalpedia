-- Prove2me | solution 3 for AvramDividend.Classical.vcstar_smooth_below_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:02:40.404014+00:00
-- url     : https://prove2.me/submissions/1091778d-a2d0-4f78-b283-c3589f89090c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) := by
  obtain ⟨_, _, _, hregular⟩ :=
    vcstar_unrestricted_verification_regularity X hX q hq W hW hc h_smooth
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W} ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact hy.1
  exact ⟨fun hnbv => (hregular.1 hnbv).mono hsubset,
    fun hbv => (hregular.2 hbv).mono hsubset⟩
