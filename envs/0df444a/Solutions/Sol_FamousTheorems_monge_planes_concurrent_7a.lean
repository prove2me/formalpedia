-- Prove2me | solution 1 for FamousTheorems.monge_planes_concurrent_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:10:40.099811+00:00
-- url     : https://prove2.me/submissions/9ed6b560-b306-42cd-8eef-054de7bd3c07

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] {n : ℕ}
    (s : Affine.Simplex ℝ P (n + 2)) : ∃ p : P, ∀ i₁ i₂ : Fin (n + 3), p ∈ s.mongePlane i₁ i₂ :=
  ⟨s.mongePoint, fun _ _ => s.mongePoint_mem_mongePlane⟩
