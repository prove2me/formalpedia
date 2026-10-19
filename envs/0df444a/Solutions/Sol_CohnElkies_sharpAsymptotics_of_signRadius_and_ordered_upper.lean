-- Prove2me | solution 1 for CohnElkies.sharpAsymptotics_of_signRadius_and_ordered_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:35.271862+00:00
-- url     : https://prove2.me/submissions/cdfe4302-2b42-46de-b32c-a7e54a401499

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_uniformAdmissibleLowerBound_of_signRadius
import Theorems.Thm_CohnElkies_sharpAsymptotics_of_uniform_lower_and_ordered_upper

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
    (hsign : UniformAntiFourierSignRadius)
    (construction : OrderedEpsilonUpperConstruction) :
    SharpQuotientAsymptotic ∧ SharpPackingRootAsymptotic ∧
      SharpLogAsymptotic ∧ SharpBinaryLogAsymptotic :=
  sharpAsymptotics_of_uniform_lower_and_ordered_upper
    (uniformAdmissibleLowerBound_of_signRadius hsign) construction
end CohnElkies
