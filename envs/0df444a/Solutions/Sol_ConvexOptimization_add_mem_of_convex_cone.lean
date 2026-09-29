-- Prove2me | solution 1 for ConvexOptimization.add_mem_of_convex_cone
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T04:48:18.621547+00:00
-- url     : https://prove2.me/submissions/34100613-f7b9-4ad8-96e3-de5424fe725c

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {d : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (u v : EuclideanSpace ℝ (Fin d)) (hu : u ∈ K) (hv : v ∈ K) :
    u + v ∈ K := by
  have hmid : (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v ∈ K :=
    hKconv hu hv (by norm_num) (by norm_num) (by norm_num)
  have h2 := hKcone 2 (by norm_num) _ hmid
  have hEq : (2 : ℝ) • ((1 / 2 : ℝ) • u + (1 / 2 : ℝ) • v) = u + v := by module
  rwa [hEq] at h2
