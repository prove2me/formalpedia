-- Prove2me | solution 1 for CohnElkies.manuscriptLinearProgram_eq_canonicalBinaryRpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/83f20f3a-86cf-4f9a-825f-9318d2f0abda

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptLinearProgram_eq_binary_error_rpow

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (hpositive : 0 < linearProgram d) :
    linearProgram d =
      (2 : ℝ) ^
        (-(criticalBinaryExponent + manuscriptBinaryExponentError d) *
          (d : ℝ)) :=
  manuscriptLinearProgram_eq_binary_error_rpow hd hpositive
end CohnElkies
