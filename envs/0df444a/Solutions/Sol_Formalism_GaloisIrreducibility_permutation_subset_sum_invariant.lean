-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.permutation_subset_sum_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:55.048883+00:00
-- url     : https://prove2.me/submissions/9136fa8e-2258-48dc-92ed-647f753b92d1

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_exists_invariant_of_isSubSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : PermSubSumInv := by
  intro α _ _ σ a h
  obtain ⟨A, hA, hcard⟩ := exists_invariant_of_isSubSum σ a h
  exact ⟨A, hA, hcard⟩
end Formalism.GaloisIrreducibility
