-- Prove2me | solution 1 for FamousTheorems.holomorphic_compact_manifold_const_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:20:36.250921+00:00
-- url     : https://prove2.me/submissions/b9b12fac-1cf3-46aa-91f6-d687671a81f5

import Mathlib

theorem solution {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless] [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] [CompactSpace M] [PreconnectedSpace M] {f : M → F}
    (hf : MDifferentiable I (modelWithCornersSelf ℂ F) f) : ∃ v : F, f = Function.const M v :=
  hf.exists_eq_const_of_compactSpace
