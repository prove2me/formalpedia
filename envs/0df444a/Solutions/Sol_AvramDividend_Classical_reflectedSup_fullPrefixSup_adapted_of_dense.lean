-- Prove2me | solution 1 for AvramDividend.Classical.reflectedSup_fullPrefixSup_adapted_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:21:45.9147+00:00
-- url     : https://prove2.me/submissions/03bac9ba-9a76-4cc6-afa9-76f07a596a92

import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_AvramDividend_Classical_reflectedSup_adapted
import Theorems.Thm_AvramDividend_Classical_reflectedSup_right_continuous
import Theorems.Thm_AvramDividend_Classical_reflectedSup_upperSemicontinuousOn_Icc
import Theorems.Thm_AvramDividend_Classical_dense_timeSup_with_endpoint
import Theorems.Thm_AvramDividend_Classical_countable_pastSup_adapted_of_adapted
open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Set ℝ≥0) (hS : S.Countable) (hDense : Dense S)
    (h0 : (0 : ℝ≥0) ∈ S) :
    Adapted 𝓕 (fun t ω =>
      ⨆ s : Set.Icc (0 : ℝ≥0) t, reflectedSup X s.1 ω) := by
  intro t
  have hc := countable_pastSup_adapted_of_adapted _ (reflectedSup_adapted X) S hS t
  have hr := reflectedSup_adapted X t
  have heq : (fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) t, reflectedSup X s.1 ω) =
      fun ω => max (⨆ s : {s : ℝ≥0 // s ∈ S ∧ s ≤ t}, reflectedSup X s.1 ω) (reflectedSup X t ω) := by
    funext ω
    apply dense_timeSup_with_endpoint _ (reflectedSup_right_continuous X ω) S hDense h0 t
    have hb := (reflectedSup_upperSemicontinuousOn_Icc X ω t).bddAbove_of_isCompact isCompact_Icc
    obtain ⟨M, hM⟩ := hb
    refine ⟨M, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact hM ⟨s.1, s.2, rfl⟩
  simp only at heq ⊢
  rw [heq]
  exact hc.max hr
