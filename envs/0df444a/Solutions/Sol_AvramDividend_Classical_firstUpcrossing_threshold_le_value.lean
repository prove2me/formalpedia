-- Prove2me | solution 1 for AvramDividend.Classical.firstUpcrossing_threshold_le_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:20:12.357456+00:00
-- url     : https://prove2.me/submissions/595c3470-c334-4957-84c9-87fca7721af4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    b ≤ X.X u ω := by
  by_contra h
  have hlt : X.X u ω < b := lt_of_not_ge h
  have htail : {t : ℝ≥0 | X.X t ω < b} ∈ 𝓝[≥] u :=
    (X.rightCont ω u).eventually (Iio_mem_nhds hlt)
  obtain ⟨v, hv, hsub⟩ :=
    mem_nhdsGE_iff_exists_Ico_subset.mp htail
  have huv : u < v := Set.mem_Ioi.mp hv
  have hpre : ∀ t : ℝ≥0, t < u → X.X t ω ≤ b := by
    intro t ht
    by_contra hne
    have hgt : b < X.X t ω := lt_of_not_ge hne
    have hinf :
        (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) ≤
          (t : ℝ≥0∞) := by
      exact iInf_le_of_le t
        (iInf_le (fun _ : b < X.X t ω => (t : ℝ≥0∞)) hgt)
    rw [← hu] at hinf
    exact (not_le_of_gt ((ENNReal.coe_lt_coe).mpr ht)) hinf
  have hvle (t : ℝ≥0) (ht : b < X.X t ω) : v ≤ t := by
    by_contra hne
    have htv : t < v := lt_of_not_ge hne
    rcases lt_or_ge t u with htu | htu
    · exact (not_lt_of_ge (hpre t htu)) ht
    · have hsmall : X.X t ω < b := hsub ⟨htu, htv⟩
      exact (not_lt_of_ge (le_of_lt hsmall)) ht
  have hvlb :
      (v : ℝ≥0∞) ≤
        (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞)) := by
    refine le_iInf (fun t => ?_)
    refine le_iInf (fun ht => ?_)
    exact (ENNReal.coe_le_coe).mpr (hvle t ht)
  rw [← hu] at hvlb
  exact (not_le_of_gt ((ENNReal.coe_lt_coe).mpr huv)) hvlb
