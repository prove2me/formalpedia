-- Prove2me | solution 1 for CohnElkies.sharpLog_of_sharpQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/efe70b2b-f94c-48c7-bd34-8ba4283de88e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_criticalPackingBase_pos
import Theorems.Thm_CohnElkies_log_criticalPackingBase
import Theorems.Thm_CohnElkies_sharpPackingRoot_of_sharpQuotient
import Theorems.Thm_CohnElkies_eventually_linearProgram_pos_of_sharpQuotient

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
    SharpLogAsymptotic := by
  have hroot := sharpPackingRoot_of_sharpQuotient hquotient
  unfold SharpPackingRootAsymptotic at hroot
  have hlogs := hroot.log criticalPackingBase_pos.ne'
  rw [log_criticalPackingBase] at hlogs
  unfold SharpLogAsymptotic
  refine hlogs.congr' ?_
  filter_upwards [eventually_linearProgram_pos_of_sharpQuotient hquotient]
    with d hd
  rw [Real.log_rpow hd]
  ring
end CohnElkies
