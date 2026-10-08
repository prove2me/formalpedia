-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_continuous_of_zero_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:22:00.932213+00:00
-- url     : https://prove2.me/submissions/345cdea3-51be-44b1-9b63-7c3fc5c0852d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

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
    (hzero : W 0 = 0) :
    Continuous W := by
  have hleft : ContinuousOn W (Iic (0 : ℝ)) := by
    have heq : Set.EqOn W (fun _ : ℝ => 0) (Iic 0) := by
      intro z hz
      by_cases hzneg : z < 0
      · exact hW.1 z hzneg
      · have hz0 : z = 0 := le_antisymm hz (le_of_not_gt hzneg)
        simpa [hz0, hzero]
    exact continuousOn_const.congr heq
  have hright : ContinuousOn W (Ici (0 : ℝ)) :=
    hW.2.2.1
  have hunion :
      ContinuousOn W (Iic (0 : ℝ) ∪ Ici 0) :=
    hleft.union_of_isClosed hright isClosed_Iic isClosed_Ici
  have hfull : Iic (0 : ℝ) ∪ Ici 0 = Set.univ := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total z 0
  simpa [hfull] using hunion
