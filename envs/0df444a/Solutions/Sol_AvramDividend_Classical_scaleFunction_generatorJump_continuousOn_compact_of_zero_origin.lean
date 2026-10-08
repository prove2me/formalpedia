-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:28:49.853829+00:00
-- url     : https://prove2.me/submissions/a1528787-1014-46f0-9da4-c46b604bd3a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_continuousAt_of_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity

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
    (hzero : W 0 = 0)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by
  have hglobal : Continuous W :=
    scaleFunction_continuous_of_zero_origin X q W hW hzero
  have hderiv : ContinuousOn (deriv W) (Ioo 0 a) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hae : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x := by
    intro x hx
    have hxa : x ∈ Ioo (0 : ℝ) a :=
      ⟨lt_of_lt_of_le hl hx.1, lt_of_le_of_lt hx.2 hu⟩
    have hD : ContinuousAt (deriv W) x :=
      hderiv.continuousAt (isOpen_Ioo.mem_nhds hxa)
    filter_upwards [] with y
    exact (generatorIntegrand_continuousAt_of_continuous
      W x y hglobal.continuousAt hglobal.continuousAt hD).continuousWithinAt
  exact scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
    X q W hW a l u hl hlu hu hC2 hae
