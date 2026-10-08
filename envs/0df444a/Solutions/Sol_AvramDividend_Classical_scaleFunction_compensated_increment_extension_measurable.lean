-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_compensated_increment_extension_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:53:51.572448+00:00
-- url     : https://prove2.me/submissions/9d5c2e7d-3d4a-4bc3-ba00-6915abd6241d

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
    (a : ℝ) (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    Measurable (fun p : ℝ × ℝ =>
      W (p.1 + p.2) - W p.1 -
      ((Ioo 0 a).indicator (deriv W) p.1) * p.2 *
        ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.2)) := by
  classical
  have hmono : Monotone W := by
    intro u v huv
    by_cases hv : v < 0
    · have hu : u < 0 := lt_of_le_of_lt huv hv
      rw [hW.1 u hu, hW.1 v hv]
    · have hv0 : 0 ≤ v := le_of_not_gt hv
      by_cases hu : u < 0
      · rw [hW.1 u hu]
        exact hW.2.1 v hv0
      · exact hW.2.2.2.1 (le_of_not_gt hu) hv0 huv
  have hmeasW : Measurable W := hmono.measurable
  have hdercont : ContinuousOn (deriv W) (Ioo 0 a) :=
    hC2.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hD : Measurable ((Ioo 0 a).indicator (deriv W)) := by
    have hpiece : Measurable
        ((Ioo 0 a).piecewise (deriv W) (fun _ : ℝ => (0 : ℝ))) :=
      hdercont.measurable_piecewise continuousOn_const isOpen_Ioo.measurableSet
    convert hpiece using 1
    funext z
    by_cases hz : z ∈ Ioo 0 a
    · simp [Set.indicator, Set.piecewise, hz]
    · simp [Set.indicator, Set.piecewise, hz]
  have hI : Measurable
      ((Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Ioo
  have hm1 : Measurable (fun p : ℝ × ℝ => W (p.1 + p.2)) :=
    hmeasW.comp (measurable_fst.add measurable_snd)
  have hm2 : Measurable (fun p : ℝ × ℝ => W p.1) :=
    hmeasW.comp measurable_fst
  have hm3 : Measurable
      (fun p : ℝ × ℝ => (Ioo 0 a).indicator (deriv W) p.1) :=
    hD.comp measurable_fst
  have hm4 : Measurable
      (fun p : ℝ × ℝ =>
        (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) p.2) :=
    hI.comp measurable_snd
  exact (hm1.sub hm2).sub ((hm3.mul measurable_snd).mul hm4)
