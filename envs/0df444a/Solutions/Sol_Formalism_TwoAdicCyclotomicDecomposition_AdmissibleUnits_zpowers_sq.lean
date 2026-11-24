-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.zpowers_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:37:20.708214+00:00
-- url     : https://prove2.me/submissions/aceb9e3d-64d0-4490-b9a2-db237a74c8dd

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_AdmissibleUnits_mem_zpowers_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
namespace Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
theorem _root_.solution {G : Type*} [Group G] [Finite G] {g y : G} (hg : g ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers g) : y = 1 ∨ y = g := by
  obtain ⟨k, rfl⟩ := mem_zpowers_nat hy
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [pow_mul, hg, one_pow]
  · right
    rw [pow_succ, pow_mul, hg, one_pow, one_mul]
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
