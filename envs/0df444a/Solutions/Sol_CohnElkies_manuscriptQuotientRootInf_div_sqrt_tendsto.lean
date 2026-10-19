-- Prove2me | solution 1 for CohnElkies.manuscriptQuotientRootInf_div_sqrt_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.874095+00:00
-- url     : https://prove2.me/submissions/ec85009b-ce71-4a4a-9c36-4e1266d53fc3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_manuscriptQuotientRootInf_div_sqrt_eq

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
    (hquotient : SharpQuotientAsymptotic) :
    Tendsto
      (fun d : ℕ =>
        sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ))
      atTop (nhds ((Real.pi)⁻¹)) := by
  change Tendsto
    (fun d : ℕ =>
      sInf (manuscriptQuotientRootSet d) / Real.sqrt (d : ℝ))
    atTop (nhds criticalRadius)
  unfold SharpQuotientAsymptotic at hquotient
  exact hquotient.congr'
    (Filter.Eventually.of_forall fun d =>
      (manuscriptQuotientRootInf_div_sqrt_eq d).symm)
end CohnElkies
