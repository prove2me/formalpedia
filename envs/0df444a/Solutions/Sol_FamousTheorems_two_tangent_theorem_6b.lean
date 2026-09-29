-- Prove2me | solution 1 for FamousTheorems.two_tangent_theorem_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:23:04.547886+00:00
-- url     : https://prove2.me/submissions/1bd316a2-ec5a-479a-b39b-e83ddd7d7b5f

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {s : EuclideanGeometry.Sphere P} {p₁ p₂ q : P} {as₁ as₂ : AffineSubspace ℝ P}
    (h₁ : s.IsTangentAt p₁ as₁) (h₂ : s.IsTangentAt p₂ as₂) (hq₁ : q ∈ as₁) (hq₂ : q ∈ as₂) :
    dist q p₁ = dist q p₂ :=
  h₁.dist_eq_of_mem_of_mem h₂ hq₁ hq₂
