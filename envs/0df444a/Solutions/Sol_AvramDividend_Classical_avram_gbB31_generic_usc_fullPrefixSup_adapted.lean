-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB31_generic_usc_fullPrefixSup_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:01:06.985951+00:00
-- url     : https://prove2.me/submissions/7f1c7b26-e752-496d-8eb6-feca28fe19b3

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
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
    (hDense : Dense S) (h0 : (0 : ℝ≥0) ∈ S) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : Set.Icc (0 : ℝ≥0) t, U s.1 ω) := by 
  intro t
  have hc := countable_pastSup_adapted_of_adapted U hAdapt S hS t
  have hr := hAdapt t
  have heq : (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, U s.1 ω) =
      fun ω => max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, U s.1 ω)
        (U t ω) := by
    funext ω
    apply dense_timeSup_with_endpoint _ (hRight ω) S hDense h0 t
    have hb := (hUSC ω t).bddAbove_of_isCompact isCompact_Icc
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hM ⟨s.1, s.2, rfl⟩
  simp only at heq ⊢
  rw [heq]
  exact hc.max hr
