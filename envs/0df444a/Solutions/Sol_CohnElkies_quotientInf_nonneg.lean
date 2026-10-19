-- Prove2me | solution 1 for CohnElkies.quotientInf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:34.337066+00:00
-- url     : https://prove2.me/submissions/1326fefb-2397-4442-b3bf-7eb7416ff496

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
theorem _root_.solution
    (d : ℕ) (hadmissible : Nonempty (Admissible d)) :
    0 ≤ sInf (quotientSet d) := by
  obtain ⟨f⟩ := hadmissible
  refine le_csInf ⟨quotient f, f, rfl⟩ ?_
  rintro _ ⟨g, rfl⟩
  exact (quotient_pos g).le
end CohnElkies
