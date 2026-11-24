-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.orbit_subset_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:58.298968+00:00
-- url     : https://prove2.me/submissions/4ff4dfa9-78a1-43b2-b3d0-0ff86890dddd

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_OrbitSubSum
import Theorems.Thm_Formalism_GaloisIrreducibility_invariant_multiset_orbit_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Classical
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : OrbitSubSum := by
  intro α ι f O I M' hO hle hM
  exact invariant_multiset_orbit_sum f O I M' hO hle hM
end Formalism.GaloisIrreducibility
