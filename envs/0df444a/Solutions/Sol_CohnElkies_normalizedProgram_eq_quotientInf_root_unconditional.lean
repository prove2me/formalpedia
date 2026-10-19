-- Prove2me | solution 1 for CohnElkies.normalizedProgram_eq_quotientInf_root_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/6a819f0d-2c83-4853-9f30-c7fdadb69d61

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_normalizedProgram_eq_quotientInf_root
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
    normalizedProgram d =
      quotientRootMap d (sInf (quotientSet d)) :=
  normalizedProgram_eq_quotientInf_root d (admissible_nonempty d)
end CohnElkies
