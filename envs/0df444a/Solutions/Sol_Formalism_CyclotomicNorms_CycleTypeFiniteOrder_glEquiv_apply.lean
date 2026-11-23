-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.glEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:27.454809+00:00
-- url     : https://prove2.me/submissions/07509f4a-e8af-479b-91d5-36e502363aea

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {K : Type*} [Field K] {N : ℕ}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (A : GL (Fin N) K) (x : Fin N → K) : glEquiv A x = repGL A x := rfl
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
