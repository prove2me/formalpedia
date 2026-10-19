-- Prove2me | solution 1 for CohnElkies.quotientSet_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/de6d805a-f4cf-49da-86c7-c36e1999a761

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotient_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory
open scoped FourierTransform SchwartzMap
namespace CohnElkies
theorem _root_.solution (d : ℕ) : BddBelow (quotientSet d) := by
  refine ⟨0, ?_⟩
  rintro y ⟨f, rfl⟩
  exact (quotient_pos f).le
end CohnElkies
