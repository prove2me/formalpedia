-- Prove2me | solution 1 for FamousTheorems.circumsphere_exists_unique_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:22:31.429976+00:00
-- url     : https://prove2.me/submissions/8bab3c30-62a6-431c-ba85-46e7cdddbe42

import Mathlib

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    {ι : Type*} [Nonempty ι] [Finite ι] {p : ι → P} (hp : AffineIndependent ℝ p) :
    ∃! cs : EuclideanGeometry.Sphere P,
      cs.center ∈ affineSpan ℝ (Set.range p) ∧ Set.range p ⊆ Metric.sphere cs.center cs.radius :=
  hp.existsUnique_dist_eq
