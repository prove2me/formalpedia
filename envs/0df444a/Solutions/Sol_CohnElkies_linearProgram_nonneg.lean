-- Prove2me | solution 1 for CohnElkies.linearProgram_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/7bdc42b5-518b-4bf4-8490-913b866b0399

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_geometricFactor_pos
import Theorems.Thm_CohnElkies_quotientInf_nonneg_unconditional

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution (d : ℕ) : 0 ≤ linearProgram d := by
  unfold linearProgram
  exact mul_nonneg (geometricFactor_pos d).le
    (quotientInf_nonneg_unconditional d)
end CohnElkies
