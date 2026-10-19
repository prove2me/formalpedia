-- Prove2me | solution 1 for CohnElkies.sharpQuotient_of_uniform_lower_and_ordered_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.753002+00:00
-- url     : https://prove2.me/submissions/cb9254e9-a026-4dd7-93cd-52e1917eadcc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_sharpQuotient_of_uniform_lower_and_constructive_upper
import Theorems.Thm_CohnElkies_constructivePrimal_of_orderedEpsilon

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
    SharpQuotientAsymptotic := by
  exact sharpQuotient_of_uniform_lower_and_constructive_upper hlower
    (constructivePrimal_of_orderedEpsilon construction)
end CohnElkies
