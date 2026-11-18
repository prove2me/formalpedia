-- Prove2me | solution 1 for FasterDistributedMatching.ApproximateMatching.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T18:19:19.747749+00:00
-- url     : https://prove2.me/submissions/b2ba3a2b-f485-47f3-868f-6655840913ae

import Theorems.Thm_DistributedRounding_weighted_average_coloring
import Theorems.Thm_FasterDistributedMatching_ApproximateMatching_pairwise_rounding_from_coloring

open FasterDistributedMatching.ApproximateMatching

theorem solution :
    ∃ (A : Deterministic (ℝ × ℕ) ObjectiveInput ℕ) (C : ℝ), 0 < C ∧
      (∀ lambda zeta, 0 < lambda → lambda ≤ 1 / 2 →
        A.program.rounds (lambda,zeta) ≤ budget C
          ((logTwo (1 / lambda)) ^ 2 + logTwo (1 / lambda) * (logStar zeta : ℝ))) ∧
      ∀ (N : ℕ) (D : PairwiseInstance N) (lambda : ℝ) (zeta : ℕ)
        (col : Fin N → ℕ), ValidObjective D lambda → Proper D.graph zeta col →
        finiteExpectation D (utility D) - finiteExpectation D (cost D) ≥
          (1 / 2) * finiteExpectation D (utility D) →
        ∀ ids : Fin N → ℕ, Function.Injective ids →
          let s := execute A D.graph (lambda,zeta) ids (objectiveInput D ids col)
          (∀ v, s v ∈ D.labels v ∧ 0 < D.probability v (s v)) ∧
          utility D s - cost D s ≥
            (9 / 10) * (finiteExpectation D (utility D) - finiteExpectation D (cost D)) := by
  obtain ⟨W,B,hB,hTime,hColor⟩ := DistributedRounding.weighted_average_coloring
  exact FasterDistributedMatching.ApproximateMatching.pairwise_rounding_from_coloring W B hB hTime hColor
