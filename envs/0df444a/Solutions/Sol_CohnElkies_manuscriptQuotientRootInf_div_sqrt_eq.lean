-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootInf_div_sqrt_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/fa862081-683a-47ee-aa36-2d0cac8d566c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptQuotientRootInf_eq
import Theorems.Thm_CohnElkies_manuscriptNormalizedQuotientInfRoot_eq

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
    sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ) =
      normalizedProgram d := by
  rw [manuscriptQuotientRootInf_eq]
  exact manuscriptNormalizedQuotientInfRoot_eq d
end CohnElkies
