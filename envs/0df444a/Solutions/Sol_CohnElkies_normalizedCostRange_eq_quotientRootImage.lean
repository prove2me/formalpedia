-- Prove2me | solution 1 for CohnElkies.normalizedCostRange_eq_quotientRootImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/9e4c2938-d404-4467-a848-ce9a665d5f33

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    Set.range (normalizedCost (d := d)) =
      quotientRootMap d '' quotientSet d := by
  ext y
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨quotient f, ⟨f, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨f, rfl⟩
end CohnElkies
