-- Prove2me | solution 1 for AvramDividend.Classical.generator_residual_continuousOn_compact_of_C2_jump_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:24:30.188567+00:00
-- url     : https://prove2.me/submissions/ef3bfcd1-9e8f-448d-b094-9f008cd4b581

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_of_continuous_components
import Theorems.Thm_AvramDividend_Classical_contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo

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
    (q : ℝ) (W : ℝ → ℝ)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      (Icc l u)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) := by
  have hsub : Icc l u ⊆ Ioo (0 : ℝ) a := by
    intro z hz
    exact ⟨lt_of_lt_of_le hl hz.1, lt_of_le_of_lt hz.2 hu⟩
  have hW : ContinuousOn W (Icc l u) :=
    hC2.continuousOn.mono hsub
  have hD : ContinuousOn (deriv W) (Icc l u) :=
    (hC2.continuousOn_deriv_of_isOpen
      isOpen_Ioo (by norm_num)).mono hsub
  have hD2 : ContinuousOn (iteratedDeriv 2 W) (Icc l u) :=
    (contDiffOn_two_continuousOn_iteratedDeriv_two_Ioo
      W a hC2).mono hsub
  exact generator_residual_continuousOn_of_continuous_components
    X q W (Icc l u) hW hD hD2 hJ
