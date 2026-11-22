-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:42.264943+00:00
-- url     : https://prove2.me/submissions/c2b623a0-4a58-4588-a5f6-b09696b00799

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
theorem _root_.solution (A : GL (Fin N) K) : repGL A = Matrix.toLin' (A : Matrix (Fin N) (Fin N) K) := rfl
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
