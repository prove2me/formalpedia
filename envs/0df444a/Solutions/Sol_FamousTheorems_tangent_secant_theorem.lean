-- Prove2me | solution 1 for FamousTheorems.tangent_secant_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:14:57.355779+00:00
-- url     : https://prove2.me/submissions/8977697b-789d-48b8-b0e9-e762bdf2a813

import Mathlib

theorem solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {P : Type*} [MetricSpace P]
    [NormedAddTorsor V P] {a b t p : P} {s : EuclideanGeometry.Sphere P} (ha : a ∈ s) (hb : b ∈ s)
    (hp : p ∈ line[ℝ, a, b]) (ht : s.IsTangentAt t line[ℝ, p, t]) : dist p t ^ 2 = dist p a * dist p b :=
  EuclideanGeometry.Sphere.dist_sq_eq_mul_dist_of_tangent_and_secant ha hb hp ht
