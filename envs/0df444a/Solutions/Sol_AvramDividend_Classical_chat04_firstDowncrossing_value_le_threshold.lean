-- Prove2me | solution 1 for AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:54:55.560722+00:00
-- url     : https://prove2.me/submissions/96c8a08d-e3d7-467b-9bd6-c84b924f4e83

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightNhds
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
    (b : ℝ) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞))) :
    X.X u ω ≤ b := by
  by_contra h
  have hgt : b < X.X u ω := lt_of_not_ge h
  have htail : {t : ℝ≥0 | b < X.X t ω} ∈ 𝓝[≥] u :=
    (X.rightCont ω u).eventually (Ioi_mem_nhds hgt)
  obtain ⟨v, hv, hsub⟩ :=
    mem_nhdsGE_iff_exists_Ico_subset.mp htail
  have huv : u < v := Set.mem_Ioi.mp hv
  have hpre : ∀ t : ℝ≥0, t < u → b ≤ X.X t ω := by
    intro t ht
    by_contra hne
    have hlt : X.X t ω < b := lt_of_not_ge hne
    have hinf :
        (⨅ (s : ℝ≥0) (_ : X.X s ω < b), (s : ℝ≥0∞)) ≤
          (t : ℝ≥0∞) := by
      exact iInf_le_of_le t
        (iInf_le (fun _ : X.X t ω < b => (t : ℝ≥0∞)) hlt)
    rw [← hu] at hinf
    exact (not_le_of_gt ((ENNReal.coe_lt_coe).mpr ht)) hinf
  have hvle (t : ℝ≥0) (ht : X.X t ω < b) : v ≤ t := by
    by_contra hne
    have htv : t < v := lt_of_not_ge hne
    rcases lt_or_ge t u with htu | htu
    · exact (not_lt_of_ge (hpre t htu)) ht
    · have hsmall : b < X.X t ω := hsub ⟨htu, htv⟩
      exact (not_lt_of_ge (le_of_lt hsmall)) ht
  have hvlb :
      (v : ℝ≥0∞) ≤
        (⨅ (t : ℝ≥0) (_ : X.X t ω < b), (t : ℝ≥0∞)) := by
    refine le_iInf (fun t => ?_)
    refine le_iInf (fun ht => ?_)
    exact (ENNReal.coe_le_coe).mpr (hvle t ht)
  rw [← hu] at hvlb
  exact (not_le_of_gt ((ENNReal.coe_lt_coe).mpr huv)) hvlb
