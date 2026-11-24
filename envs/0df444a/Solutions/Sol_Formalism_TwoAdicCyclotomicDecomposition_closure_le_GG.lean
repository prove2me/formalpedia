-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.closure_le_GG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:11.225805+00:00
-- url     : https://prove2.me/submissions/3b6cf9b5-f088-484d-9b83-48830b4cb3b6

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NegOneNeOneUnitsZmodFour
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_resMap_apply
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_mem_GG
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_um_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution {s m : ℕ} (h : s ≤ m) :
    Subgroup.closure {((-1, 1, 1) : GalL (m + 2)), ((u5 (m + 2) ^ (2 ^ s), 1, 1) : GalL (m + 2))}
      ≤ GG h := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [SetLike.mem_coe, mem_GG, resMap_apply, unitsMap_neg_one']
    exact Subgroup.mem_zpowers _
  · rw [SetLike.mem_coe, mem_GG, resMap_apply, show u5 (m + 2) ^ (2 ^ s) = wgen s m from rfl, um_w h]
    exact Subgroup.one_mem _
end Formalism.TwoAdicCyclotomicDecomposition
