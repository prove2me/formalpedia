-- Prove2me | solution 1 for CohnElkies.sharpAsymptotics_of_uniform_lower_and_ordered_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/d236ca2a-aca9-41ba-b170-59db669a2737

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpQuotient_of_uniform_lower_and_ordered_upper
import Theorems.Thm_CohnElkies_sharpPackingRoot_of_sharpQuotient
import Theorems.Thm_CohnElkies_sharpLog_of_sharpQuotient
import Theorems.Thm_CohnElkies_sharpBinaryLog_of_sharpQuotient

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
    (hlower : UniformAdmissibleLowerBound)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic := by
  have hquotient :=
    sharpQuotient_of_uniform_lower_and_ordered_upper hlower construction
  exact ⟨hquotient, sharpPackingRoot_of_sharpQuotient hquotient,
    sharpLog_of_sharpQuotient hquotient,
    sharpBinaryLog_of_sharpQuotient hquotient⟩
end CohnElkies
