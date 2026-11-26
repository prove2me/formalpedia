-- Prove2me | solution 1 for Eden.embedFour_mem_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:54.695079+00:00
-- url     : https://prove2.me/submissions/ccbb7744-306c-4c2b-8e8d-9f7d1955e2f9

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Definitions.Def_Eden_HausdorffGeometry

set_option autoImplicit true
noncomputable section
open Set MeasureTheory
open Eden
namespace Eden
theorem _root_.solution {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ∈ euclideanOpenCube 4) : embedFour x ∈ attractor := by
  have hs (i : Fin 4) : x i ^ 2 < 1 := by
    have hi := abs_lt.mp (hx i)
    nlinarith [mul_pos (by linarith : 0 < 1 - x i) (by linarith : 0 < 1 + x i)]
  change x 0 ^ 2 + x 1 ^ 2 ≤ 2 ∧ x 2 ^ 2 + x 3 ^ 2 ≤ 2 ∧ (0 : ℝ) = 0
  exact ⟨by linarith [hs 0, hs 1], by linarith [hs 2, hs 3], rfl⟩
end Eden
