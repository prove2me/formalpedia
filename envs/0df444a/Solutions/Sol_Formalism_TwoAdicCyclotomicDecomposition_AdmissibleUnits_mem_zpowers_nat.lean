-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits.mem_zpowers_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:05.837631+00:00
-- url     : https://prove2.me/submissions/3f24ce34-fbb1-4845-a500-c3a45697caeb

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OrderOfThreeUnitsTwoPow

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
theorem _root_.solution {G : Type*} [Group G] [Finite G] {x y : G}
    (h : y ∈ Subgroup.zpowers x) : ∃ k : ℕ, x ^ k = y := by
  exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h)
end Formalism.TwoAdicCyclotomicDecomposition.AdmissibleUnits
