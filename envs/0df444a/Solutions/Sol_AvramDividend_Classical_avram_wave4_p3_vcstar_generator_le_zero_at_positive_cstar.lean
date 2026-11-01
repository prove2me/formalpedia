-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p3_vcstar_generator_le_zero_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:05:22.892415+00:00
-- url     : https://prove2.me/submissions/e512172d-6b8d-4f96-baff-3f2506ee217c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual generator residual is nonpositive at the positive optimal cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hcpos : 0 < cstar W)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal ≤ 0 := by
  obtain ⟨hdom, hmax⟩ :=
    vcstar_hjb_at_positive_cstar X hX q hq W hW hc h_smooth hcpos hgen
  refine ⟨hdom, ?_⟩
  calc
    X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal ≤
      max (X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal)
        (1 - deriv (vcstar W) (cstar W).toReal) :=
      le_max_left _ _
    _ = 0 := hmax
