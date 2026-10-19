-- Prove2me | solution 1 for CohnElkies.monotoneOn_quotientRootMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/98cf446a-c591-4d79-9a91-4ad267ee6964

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotient_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Set
namespace CohnElkies
theorem _root_.solution (d : ℕ) :
    MonotoneOn (quotientRootMap d) (quotientSet d) := by
  intro x hx y _ hxy
  rcases hx with ⟨f, rfl⟩
  unfold quotientRootMap
  exact div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (quotient_pos f).le hxy (by positivity))
    (Real.sqrt_nonneg _)
end CohnElkies
