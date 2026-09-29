-- Prove2me | solution 1 for Erdos146.hammingRetentionMeasure_real_contains_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:29:19.738085+00:00
-- url     : https://prove2.me/submissions/75deb2d4-73bc-429b-a73a-319cd7fe28ea

import Definitions.Def_erdos146_core2
import Mathlib.Probability.Distributions.SetBernoulli

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (hammingRetentionMeasure dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      hammingRetentionProbability dimension ^ required.card := by
  classical
  have hpreimage :
      (fun membership : (Bool × HammingWord dimension) → Prop =>
        {vertex | membership vertex}) ⁻¹'
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        Set.pi (required : Set (Bool × HammingWord dimension))
          (fun _ => ({True} : Set Prop)) := by
    ext membership
    simp
  have hmeasure :
      hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        (↑(unitInterval.toNNReal
          (hammingRetentionParameter dimension)) : ENNReal) ^
            required.card := by
    unfold hammingRetentionMeasure
    rw [ProbabilityTheory.setBernoulli_apply']
    rw [hpreimage]
    rw [MeasureTheory.Measure.infinitePi_pi]
    · simp
    · intro vertex _
      measurability
  change
    ENNReal.toReal
        (hammingRetentionMeasure dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained}) = _
  rw [hmeasure, ENNReal.toReal_pow]
  simp [hammingRetentionParameter]
