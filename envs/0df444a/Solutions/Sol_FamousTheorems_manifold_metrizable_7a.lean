-- Prove2me | solution 1 for FamousTheorems.manifold_metrizable_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:14:49.425643+00:00
-- url     : https://prove2.me/submissions/2fd7c2a6-9d02-4958-9549-21e9cb568764

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [SigmaCompactSpace M]
    [T2Space M] : TopologicalSpace.MetrizableSpace M :=
  Manifold.metrizableSpace I M
