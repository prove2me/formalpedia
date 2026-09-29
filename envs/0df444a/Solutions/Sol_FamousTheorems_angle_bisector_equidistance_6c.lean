-- Prove2me | solution 1 for FamousTheorems.angle_bisector_equidistance_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:14:11.606447+00:00
-- url     : https://prove2.me/submissions/6d504ab5-aa1d-46db-9d84-cd416c958e7a

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {p p' : P} {s₁ s₂ : AffineSubspace ℝ P} [s₁.direction.HasOrthogonalProjection]
    [s₂.direction.HasOrthogonalProjection] (hp'₁ : p' ∈ s₁) (hp'₂ : p' ∈ s₂) [Nonempty s₁] [Nonempty s₂] :
    dist p (orthogonalProjection s₁ p : P) = dist p (orthogonalProjection s₂ p : P) ↔
      ∠ p p' (orthogonalProjection s₁ p : P) = ∠ p p' (orthogonalProjection s₂ p : P) :=
  dist_orthogonalProjection_eq_iff_angle_eq hp'₁ hp'₂
