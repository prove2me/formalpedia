-- Prove2me | solution 1 for EdenVerified.s11_first_circle_in_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:53:03.308818+00:00
-- url     : https://prove2.me/submissions/464bacf6-f60a-4aa1-a03a-aa676836662e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_firstCircle_unstableInPlane


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 0, Metric.infDist p (firstCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (firstCircle 1) :=
  firstCircle_unstableInPlane c
end EdenVerified
