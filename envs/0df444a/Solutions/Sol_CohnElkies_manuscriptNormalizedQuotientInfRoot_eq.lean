-- Prove2me | solution 1 for CohnElkies.manuscriptNormalizedQuotientInfRoot_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/7cd4c15b-2a9b-4d05-9b98-1fca46dc0f52

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedProgram_eq_quotientInf_root_unconditional

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
    manuscriptNormalizedQuotientInfRoot d = normalizedProgram d := by
  rw [normalizedProgram_eq_quotientInf_root_unconditional]
  rfl
end CohnElkies
