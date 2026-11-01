-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_iff_above_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:15:36.697255+00:00
-- url     : https://prove2.me/submissions/29876b2f-0ee1-4354-9ec5-dedd418d0d32

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_residual_only
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For a Gaussian or BV source the global HJB condition is exactly the upper residual test. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0) ↔
    (∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) := by
  constructor
  · intro hhjb y hy
    have hypos : (0 : ℝ) < y :=
      lt_of_le_of_lt ENNReal.toReal_nonneg hy
    have hmax := (hhjb y hypos).2
    calc
      X.generator (vcstar W) y - q * vcstar W y
          ≤ max (X.generator (vcstar W) y - q * vcstar W y)
              (1 - deriv (vcstar W) y) := le_max_left _ _
      _ = 0 := hmax
  · intro hres
    exact avram_wave4_05_gaussian_or_bv_hjb_residual_only
      X hX q hq W hW hbranch hres
