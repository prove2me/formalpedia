-- Prove2me | solution 1 for CohnElkies.tendsto_manuscriptQuotientRootError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/2c3bae01-cb67-4227-93c7-e4e697abce57

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpQuotientAsymptotic

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
    Tendsto manuscriptQuotientRootError atTop (nhds (0 : ℝ)) := by
  have hquotient :
      Tendsto normalizedProgram atTop (nhds criticalRadius) :=
    sharpQuotientAsymptotic
  have hconstant :
      Tendsto (fun _ : ℕ => criticalRadius) atTop
        (nhds criticalRadius) := tendsto_const_nhds
  simpa [manuscriptQuotientRootError] using!
    hquotient.sub hconstant
end CohnElkies
