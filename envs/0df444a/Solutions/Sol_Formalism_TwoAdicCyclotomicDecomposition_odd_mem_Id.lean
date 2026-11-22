-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.odd_mem_Id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:24:41.630089+00:00
-- url     : https://prove2.me/submissions/45596b1a-af4d-4353-b89e-ab91f8e5a544

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (n : ℕ) (g : GalL n) : g ∈ Id n ↔ g = 1 ∨ g = (1, 1, -1) := by
  unfold Id
  constructor
  · intro hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.units_eq_one_or ((((1, 1, -1) : GalL n) ^ k).2.2) with h | h
    · left; exact Prod.ext (by simp) (Prod.ext (by simp) h)
    · right; exact Prod.ext (by simp) (Prod.ext (by simp) h)
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact Subgroup.mem_zpowers _
end Formalism.TwoAdicCyclotomicDecomposition
