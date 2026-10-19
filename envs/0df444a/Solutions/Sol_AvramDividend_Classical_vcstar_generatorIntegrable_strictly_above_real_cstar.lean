-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_generatorIntegrable_strictly_above_real_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T06:49:54.080757+00:00
-- url     : https://prove2.me/submissions/b4b2d956-79f8-4265-8f8a-447558f4f6be

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_generatorIntegrable_above
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    X.GeneratorIntegrable (vcstar W) x := by
  change X.GeneratorIntegrable (barrierValue W (cstar W).toReal) x
  exact barrierValue_generatorIntegrable_above X q W hW
    (cstar W).toReal x ENNReal.toReal_nonneg hx
