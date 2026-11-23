-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:36.305863+00:00
-- url     : https://prove2.me/submissions/d2d58e9c-c05f-4604-9fda-a05c2dc84750

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_repGL_eq

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
theorem _root_.solution (A : GL (Fin N) K) (x : Fin N → K) :
    repGL A x = Matrix.mulVec (A : Matrix (Fin N) (Fin N) K) x := by
  rw [repGL_eq, Matrix.toLin'_apply]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
