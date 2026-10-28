-- Prove2me | solution 1 for AvramDividend.Classical.monotone_usc_capped_superlevel_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:40:46.0918+00:00
-- url     : https://prove2.me/submissions/07c739a6-21fc-450b-9f7f-16153198db54

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_AvramDividend_Classical_usc_capped_first_closed_hit_le_iff_prefix_hit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℝ≥0 → Ω → ℝ) (hu : Adapted 𝓕 u)
    (hmono : ∀ ω : Ω, Monotone (fun t => u t ω))
    (husc : ∀ (ω : Ω) (H : ℝ≥0),
      UpperSemicontinuousOn (fun t => u t ω) (Icc 0 H))
    (H : ℝ≥0) (a : ℝ) :
    IsStoppingTime 𝓕 (fun ω : Ω =>
      WithTop.some (sInf ((Icc (0 : ℝ≥0) H ∩
        (fun t : ℝ≥0 => u t ω) ⁻¹' Ici a) ∪ {H}))) := by
  intro t
  have hMeas : MeasurableSet[𝓕 t]
      {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
        (fun v : ℝ≥0 => u v ω) ⁻¹' Ici a) ∪ {H}) ≤ t} := by
    by_cases ht : t < H
    · have hEq :
        {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
          (fun v : ℝ≥0 => u v ω) ⁻¹' Ici a) ∪ {H}) ≤ t} =
        {ω : Ω | a ≤ u t ω} := by
        ext ω
        rw [Set.mem_setOf_eq, Set.mem_setOf_eq,
          usc_capped_first_closed_hit_le_iff_prefix_hit
            (fun v : ℝ≥0 => u v ω) H t a (husc ω H) ht]
        constructor
        · rintro ⟨s, hs, ha⟩
          exact ha.trans ((hmono ω) hs)
        · intro ha
          exact ⟨t, le_rfl, ha⟩
      rw [hEq]
      exact measurableSet_le measurable_const (hu t)
    · have htH : H ≤ t := le_of_not_gt ht
      have hEq :
        {ω : Ω | sInf ((Icc (0 : ℝ≥0) H ∩
          (fun v : ℝ≥0 => u v ω) ⁻¹' Ici a) ∪ {H}) ≤ t} =
        Set.univ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        have hbdd : BddBelow ((Icc (0 : ℝ≥0) H ∩
            (fun v : ℝ≥0 => u v ω) ⁻¹' Ici a) ∪ {H}) :=
          OrderBot.bddBelow _
        have hH : H ∈ ((Icc (0 : ℝ≥0) H ∩
            (fun v : ℝ≥0 => u v ω) ⁻¹' Ici a) ∪ {H}) :=
          Or.inr rfl
        exact (csInf_le hbdd hH).trans htH
      rw [hEq]
      exact MeasurableSet.univ
  simpa only [WithTop.coe_le_coe] using hMeas
