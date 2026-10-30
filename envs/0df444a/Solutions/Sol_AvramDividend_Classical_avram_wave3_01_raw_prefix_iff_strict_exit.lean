-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_raw_prefix_iff_strict_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:33:51.774894+00:00
-- url     : https://prove2.me/submissions/b69759be-6fad-4ad5-922a-1ab38243087a

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
import Theorems.Thm_AvramDividend_Classical_strict_up_before_down_preserves_lower_prefix

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- For a genuinely attained upper record, raw lower-barrier prefix survival
    is equivalent to the correct strict order of the two exit clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω) :
    (∀ t : ℝ≥0, t < u → -a ≤ X.X t ω) ↔
      (u : ℝ≥0∞) < twoSidedExitDownTime X (-a) ω := by
  constructor
  · intro hPre
    have hPeak : X.X u ω = b :=
      (firstUpcrossing_attains_peak X b hb ω u hu).1
    have hSmall : -a < X.X u ω := by rw [hPeak]; linarith
    have hevent :
        {t : ℝ≥0 | -a < X.X t ω} ∈ 𝓝[≥] u :=
      (X.rightCont ω u).tendsto.eventually (Ioi_mem_nhds hSmall)
    obtain ⟨v, hv, hsub⟩ :=
      (mem_nhdsGE_iff_exists_Ico_subset.mp hevent)
    have hbound : (v : ℝ≥0∞) ≤ twoSidedExitDownTime X (-a) ω := by
      change (v : ℝ≥0∞) ≤
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞))
      refine le_iInf fun t => le_iInf fun hBad => ?_
      apply ENNReal.coe_le_coe.mpr
      by_contra hnot
      have htv : t < v := lt_of_not_ge hnot
      by_cases htu : t < u
      · exact (not_lt_of_ge (hPre t htu)) hBad
      · have hGood : -a < X.X t ω :=
          hsub ⟨le_of_not_gt htu, htv⟩
        exact (not_lt_of_ge (le_of_lt hGood)) hBad
    exact (ENNReal.coe_lt_coe.mpr hv).trans_le hbound
  · intro hBefore
    have hUp : twoSidedExitUpTime X b ω <
        twoSidedExitDownTime X (-a) ω := by
      rw [← hu]
      exact hBefore
    intro t ht
    have ht' : (t : ℝ≥0∞) < twoSidedExitUpTime X b ω := by
      rw [← hu]
      exact ENNReal.coe_lt_coe.mpr ht
    exact strict_up_before_down_preserves_lower_prefix X b (-a) ω hUp t ht'
