-- Prove2me | solution 1 for EdenVerified.s11_second_circle_in_plane
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:52:53.210004+00:00
-- url     : https://prove2.me/submissions/4a30f08b-5148-4016-9d4d-16e61ff6a1fa

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_secondCircle_unstableInPlane


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ →
      ∃ p ∈ attractor ∩ coordinatePlane 1, Metric.infDist p (secondCircle 1) < δ ∧
        ∃ t : ℝ, 0 ≤ t ∧ ε ≤ Metric.infDist (evolution c t p) (secondCircle 1) :=
  secondCircle_unstableInPlane c
end EdenVerified
