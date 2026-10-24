-- Prove2me | solution 2 for AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:10:01.292713+00:00
-- url     : https://prove2.me/submissions/065dcddf-6638-4391-8ecc-28bb81e62c86
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_basic_boundary_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_smooth_below_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Local verification regularity splits into elementary boundary
continuity and the remaining process-level scale smoothness. -/
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
  rcases vcstar_basic_boundary_regular_of_positive_cstar
    X hX q hq W hW hc hcpos with ⟨hcontinuous, hzero, hnegative⟩
  exact ⟨hcontinuous, hzero, hnegative,
    vcstar_smooth_below_positive_cstar X hX q hq W hW hc hcpos h_smooth⟩
