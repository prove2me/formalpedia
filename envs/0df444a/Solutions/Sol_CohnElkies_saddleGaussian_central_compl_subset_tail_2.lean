-- Prove2me | solution 2 for CohnElkies.saddleGaussian_central_compl_subset_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:55:49.889439+00:00
-- url     : https://prove2.me/submissions/ea5e8d7f-2e47-4145-80db-f206d760ec06

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


theorem solution
    (R : ℝ) :
    (Icc (-R) R)ᶜ ⊆ saddleGaussianTailSet R := by
  intro T hT
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hT
  show R ≤ |T|
  rcases hT with h | h
  · have := neg_abs_le T; linarith
  · have := le_abs_self T; linarith

