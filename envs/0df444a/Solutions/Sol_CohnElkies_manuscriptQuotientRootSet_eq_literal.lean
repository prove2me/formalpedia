-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootSet_eq_literal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:38.10986+00:00
-- url     : https://prove2.me/submissions/6599e4ca-6174-4feb-94ec-c1b083d462ab

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open CohnElkies
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    manuscriptQuotientRootSet d =
      {q : ℝ | ∃ f : Admissible d,
        quotient f ^ ((d : ℝ)⁻¹) = q} := by
  ext q
  simp [manuscriptQuotientRootSet]
end CohnElkies
