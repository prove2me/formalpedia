-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_generatorIntegrand_continuousAt_away_shift_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:33:53.809+00:00
-- url     : https://prove2.me/submissions/bd53c831-099b-440f-9436-13eec8e51c99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_continuousAt_of_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x y : ℝ) (hx : x ∈ Ioo 0 a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hshift : x + y ≠ 0) :
    ContinuousAt
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y) x := by
  have hxmem : Ici (0 : ℝ) ∈ 𝓝 x := by
    apply Filter.mem_of_superset (isOpen_Ioi.mem_nhds hx.1)
    intro z hz
    exact le_of_lt (by simpa only [mem_Ioi] using hz)
  have hWx : ContinuousAt W x :=
    hW.2.2.1.continuousAt hxmem
  have hWxy : ContinuousAt W (x + y) :=
    scaleFunction_continuousAt_away_zero X q W hW (x + y) hshift
  have hDc : ContinuousOn (deriv W) (Ioo 0 a) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hDx : ContinuousAt (deriv W) x :=
    hDc.continuousAt (isOpen_Ioo.mem_nhds hx)
  exact generatorIntegrand_continuousAt_of_continuous
    W x y hWx hWxy hDx
