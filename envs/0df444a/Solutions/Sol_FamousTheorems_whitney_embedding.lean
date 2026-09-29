-- Prove2me | solution 1 for FamousTheorems.whitney_embedding
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:08:01.616778+00:00
-- url     : https://prove2.me/submissions/d1c99f4f-4424-4140-80b4-97a2fd7e6bd5

import Mathlib

open scoped ContDiff Manifold

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ) (e : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ e ∧ Topology.IsClosedEmbedding e ∧
        ∀ x : M, Function.Injective (mfderiv I (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) e x) :=
  exists_embedding_euclidean_of_compact
