-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_generator_above_eq_drift_add_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:58:03.901984+00:00
-- url     : https://prove2.me/submissions/d35a4000-2c87-4670-be0f-68fc065c005d

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_iteratedDeriv_two_eq_zero_above_cstar

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
    (W : ℝ → ℝ) (x : ℝ)
    (hx : (cstar W).toReal < x) :
    X.generator (vcstar W) x =
      X.c + ∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν := by
  unfold SpectrallyNegativeLevy.generator
  rw [vcstar_iteratedDeriv_two_eq_zero_above_cstar W x hx]
  rw [vcstar_deriv_eq_one_above_cstar W x hx]
  ring