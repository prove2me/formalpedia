-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_capped_firstClosedHit_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:38:38.539011+00:00
-- url     : https://prove2.me/submissions/7f6a606c-474a-49e0-99cf-7a649c6b75f7

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_reflectedSup_fullPrefixSup_adapted_of_dense
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}))) := by
  intro t
  simp only [WithTop.coe_le_coe]
  by_cases ht : t < H
  · have heq : {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) ≤ t} =
        {ω | x ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, reflectedSup X s.1 ω} := by
      ext ω
      simp only [mem_setOf_eq]
      rw [usc_capped_first_closed_hit_le_iff_prefix_hit (fun u => reflectedSup X u ω) H t x
        (reflectedSup_upperSemicontinuousOn_Icc X ω H) ht]
      exact usc_compact_prefix_hit_iff_ciSup_ge (fun s => reflectedSup X s ω) t x
        (reflectedSup_upperSemicontinuousOn_Icc X ω t)
    rw [heq]
    exact measurableSet_le measurable_const
      (reflectedSup_fullPrefixSup_adapted_of_dense X S hS hDense h0 t)
  · have heq : {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) ≤ t} = univ := by
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact (csInf_le (OrderBot.bddBelow _) (mem_union_right _ (mem_singleton H))).trans (le_of_not_gt ht)
    rw [heq]
    exact MeasurableSet.univ
