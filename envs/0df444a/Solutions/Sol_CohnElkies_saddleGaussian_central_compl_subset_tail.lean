-- Prove2me | solution 1 for CohnElkies.saddleGaussian_central_compl_subset_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/4dd340c6-8d8c-4e8a-962b-336471ec54d6

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    (R : ℝ) :
    (Icc (-R) R)ᶜ ⊆ saddleGaussianTailSet R := by
  intro T hT
  change R ≤ |T|
  by_contra hnot
  have hsmall : |T| < R := lt_of_not_ge hnot
  have hinterior := (abs_lt).mp hsmall
  exact hT ⟨hinterior.1.le, hinterior.2.le⟩
end CohnElkies
