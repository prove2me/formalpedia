-- Prove2me | solution 1 for CohnElkies.eventually_manuscriptLinearProgram_eq_canonicalBinaryRpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/e6577e1c-0c80-4c5a-87de-8dd07f6729e5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_manuscriptLinearProgram_pos
import Theorems.Thm_CohnElkies_manuscriptLinearProgram_eq_canonicalBinaryRpow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ d : ℕ in atTop,
      linearProgram d =
        (2 : ℝ) ^
          (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
            (d : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_manuscriptLinearProgram_pos]
    with d hd hpositive
  exact manuscriptLinearProgram_eq_canonicalBinaryRpow hd hpositive
end CohnElkies
