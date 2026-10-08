-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrable_of_vcstar_contDiff_two
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:02:50.766994+00:00
-- url     : https://prove2.me/submissions/1a2b5c2f-ae5f-4f64-a972-6da71025acbe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_below_cstar_of_vcstar
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrable_of_contDiff_two

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
    (hvc : ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal, X.GeneratorIntegrable W x := by
  have hW2 : ContDiffOn ℝ 2 W (Ioo 0 (cstar W).toReal) :=
    scaleFunction_contDiff_two_below_cstar_of_vcstar W hvc hk
  intro x hx
  exact scaleFunction_generatorIntegrable_of_contDiff_two
    X q W hW (cstar W).toReal x hx hW2
