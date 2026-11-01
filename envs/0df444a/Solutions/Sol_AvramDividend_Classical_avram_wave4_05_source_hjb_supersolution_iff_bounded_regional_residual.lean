-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_hjb_supersolution_iff_bounded_regional_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:32:56.719189+00:00
-- url     : https://prove2.me/submissions/c72b4dd2-1449-4174-bfbe-152b893dbdbc

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The entire actual-source supersolution is exactly two bounded regional tests. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0) ↔
    ((0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) ∧
      (∀ y : ℝ, (cstar W).toReal < y →
        y < (cstar W).toReal + 1 + max 0 (X.c / q) →
        X.generator (vcstar W) y - q * vcstar W y ≤ 0)) := by
  constructor
  · intro hsup
    constructor
    · intro hcpos x hx
      have hxpos : (0 : ℝ) < x := (mem_Ioo.mp hx).1
      have hsupx := hsup x hxpos
      refine ⟨hsupx.1, ?_⟩
      exact le_trans (le_max_left _ _) hsupx.2
    · intro y hy _
      have hypos : (0 : ℝ) < y :=
        lt_of_le_of_lt ENNReal.toReal_nonneg hy
      have hsupy := hsup y hypos
      exact le_trans (le_max_left _ _) hsupy.2
  · intro hregional
    exact avram_wave4_05_source_hjb_supersolution_of_bounded_strip_regional_residual
      X hX q hq W hW hsmooth hregional.2 hregional.1
