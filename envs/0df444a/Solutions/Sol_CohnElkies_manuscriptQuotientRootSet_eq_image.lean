-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootSet_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/8efdd70b-c0f9-4f25-86ed-a0ca912fe897

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    manuscriptQuotientRootSet d =
      (fun x : ℝ => x ^ ((d : ℝ)⁻¹)) '' quotientSet d := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotient f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
end CohnElkies
