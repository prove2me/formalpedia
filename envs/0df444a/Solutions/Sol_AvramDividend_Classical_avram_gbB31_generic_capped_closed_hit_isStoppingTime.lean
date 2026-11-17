-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_generic_capped_closed_hit_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:37:02.750494+00:00
-- url     : https://prove2.me/submissions/bed2252b-ade1-494c-8425-24d8ae647cd3

import Mathlib
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_generic_usc_fullPrefixSup_adapted
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit
import Theorems.Thm_AvramDividend_Classical_usc_compact_prefix_hit_iff_ciSup_ge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (U : ℝ≥0 → Ω → ℝ) (hAdapt : Adapted 𝓕 U)
    (hRight : ∀ ω (u : ℝ≥0),
      ContinuousWithinAt (fun t => U t ω) (Ici u) u)
    (hUSC : ∀ ω (t : ℝ≥0),
      UpperSemicontinuousOn (fun u => U u ω) (Icc 0 t))
    (S : Set ℝ≥0) (hS : S.Countable)
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S)
    (H : ℝ≥0) (x : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => U u ω) ⁻¹' Ici x) ∪ {H}))) := by 
  intro t
  simp only [WithTop.coe_le_coe]
  by_cases ht : t < H
  · have heq : {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => U u ω) ⁻¹' Ici x) ∪ {H}) ≤ t} =
        {ω | x ≤ ⨆ s : Set.Icc (0 : ℝ≥0) t, U s.1 ω} := by
      ext ω
      simp only [mem_setOf_eq]
      rw [usc_capped_first_closed_hit_le_iff_prefix_hit
        (fun u => U u ω) H t x (hUSC ω H) ht]
      exact usc_compact_prefix_hit_iff_ciSup_ge
        (fun s => U s ω) t x (hUSC ω t)
    rw [heq]
    exact measurableSet_le measurable_const
      (avram_gbB31_generic_usc_fullPrefixSup_adapted
        U hAdapt hRight hUSC S hS hDense h0 t)
  · have heq : {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
        (fun u : ℝ≥0 => U u ω) ⁻¹' Ici x) ∪ {H}) ≤ t} = univ := by
      ext ω
      simp only [mem_setOf_eq, mem_univ, iff_true]
      exact (csInf_le (OrderBot.bddBelow _)
        (mem_union_right _ (mem_singleton H))).trans (le_of_not_gt ht)
    rw [heq]
    exact MeasurableSet.univ
