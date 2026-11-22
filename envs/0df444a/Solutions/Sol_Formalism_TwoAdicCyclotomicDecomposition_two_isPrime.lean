-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.two_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T16:57:56.63799+00:00
-- url     : https://prove2.me/submissions/bfd499f8-c756-40cc-9169-2d3d28514b2b

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Lemmata_FirstBlockLemmaE_Imports
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution : (span {(2 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime two_ne_zero]
  exact Int.prime_two
end Formalism.TwoAdicCyclotomicDecomposition
