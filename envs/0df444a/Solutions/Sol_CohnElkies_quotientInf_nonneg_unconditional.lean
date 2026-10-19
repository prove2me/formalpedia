-- Prove2me | solution 1 for CohnElkies.quotientInf_nonneg_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/e25d332f-10ac-48cf-830e-46721d88df13

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_quotientInf_nonneg
import Theorems.Thm_CohnElkies_admissible_nonempty

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
    0 ≤ sInf (quotientSet d) :=
  quotientInf_nonneg d (admissible_nonempty d)
end CohnElkies
