-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:18:08.333143+00:00
-- url     : https://prove2.me/submissions/13eb90ee-55a9-4c40-a0fa-c5d5a6fa4036

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shift_ae_continuous_of_standing_bv
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_ae_continuousWithinAt_of_shift_ae

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
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x := by
  intro x hx
  have hxa : x ∈ Ioo (0 : ℝ) a :=
    ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
  have hx0 : x ≠ 0 := ne_of_gt hxa.1
  have hWx : ContinuousAt W x :=
    scaleFunction_continuousAt_away_zero X q W hW x hx0
  have hDc : ContinuousOn (deriv W) (Ioo 0 a) :=
    hC1.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDx : ContinuousAt (deriv W) x :=
    hDc.continuousAt (isOpen_Ioo.mem_nhds hxa)
  have hshift :
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)), ContinuousAt W (x + y) :=
    scaleFunction_shift_ae_continuous_of_standing_bv
      X hX hbv q W hW x hxa.1
  exact generatorIntegrand_ae_continuousWithinAt_of_shift_ae
    W (X.ν.restrict (Iio 0)) (Icc l u) x hWx hDx hshift
