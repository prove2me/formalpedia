-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_vcstar_original_cutoff_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:57:03.593201+00:00
-- url     : https://prove2.me/submissions/96224813-e08f-440a-a8db-5f0f3204bbb8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ y ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) y ∧
      (X.σ ^ 2 / 2 * iteratedDeriv 2 (vcstar W) y +
        (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv (vcstar W) y +
        (∫ z in Iic (-1 : ℝ), vcstar W (y + z) - vcstar W y ∂X.ν) +
        (∫ z in Ioo (-1 : ℝ) (-ε), vcstar W (y + z) - vcstar W y ∂X.ν) +
        (∫ z in Ico (-ε) 0,
          SpectrallyNegativeLevy.generatorIntegrand (vcstar W) y z ∂X.ν) -
        q * vcstar W y = 0) := by
  intro y hy
  obtain ⟨hI, hEq⟩ := generator_vcstar_eq_zero X hX q hq W hW h_smooth hc y hy
  refine ⟨hI, ?_⟩
  have hFormula :=
    avram_p4_c_generator_original_epsilon_drift_identification X (vcstar W) y
      ε hε hε1 hI
  rw [hFormula] at hEq
  exact hEq
