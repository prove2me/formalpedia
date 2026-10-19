-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_pre_ruin_strict_of_right_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T11:09:34.896029+00:00
-- url     : https://prove2.me/submissions/764364dd-64c0-478c-ba81-bf9c4c9ee84e

import Mathlib.Topology.Order.LeftRightNhds
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBefore : ∀ t : ℝ≥0, t < u → reflectedSup X t ω ≤ a)
    (hRight : ContinuousWithinAt (fun t => reflectedSup X t ω)
      (Set.Ici u) u) :
    (u : ℝ≥0∞) <
      (⨅ (t : ℝ≥0) (_ : a < reflectedSup X t ω), (t : ℝ≥0∞)) := by
  have hz : reflectedSup X u ω = 0 :=
    firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  have hsmall : reflectedSup X u ω < a := by
    simpa [hz] using ha
  have hevent : {t : ℝ≥0 | reflectedSup X t ω < a} ∈ 𝓝[≥] u :=
    hRight.tendsto.eventually (Iio_mem_nhds hsmall)
  obtain ⟨v, hv, hsub⟩ :=
    (mem_nhdsGE_iff_exists_Ico_subset.mp hevent)
  have hbound : (v : ℝ≥0∞) ≤
      (⨅ (t : ℝ≥0) (_ : a < reflectedSup X t ω), (t : ℝ≥0∞)) := by
    refine le_iInf fun t => le_iInf fun hbreach => ?_
    apply ENNReal.coe_le_coe.mpr
    by_contra hn
    have htv : t < v := lt_of_not_ge hn
    by_cases htu : t < u
    · exact (not_lt_of_ge (hBefore t htu)) hbreach
    · have hs : reflectedSup X t ω < a :=
        hsub ⟨le_of_not_gt htu, htv⟩
      exact (not_lt_of_ge (le_of_lt hs)) hbreach
  exact (ENNReal.coe_lt_coe.mpr hv).trans_le hbound
