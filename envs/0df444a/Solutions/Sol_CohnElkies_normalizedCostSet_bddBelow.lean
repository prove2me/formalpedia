-- Prove2me | solution 1 for CohnElkies.normalizedCostSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/25d58b43-2464-4839-8454-6ee31d39a253

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedCost_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    BddBelow (Set.range (normalizedCost (d := d))) := by
  refine ⟨0, ?_⟩
  rintro y ⟨f, rfl⟩
  exact normalizedCost_nonneg f
end CohnElkies
