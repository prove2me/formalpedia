-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.charpoly_repGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:26.383652+00:00
-- url     : https://prove2.me/submissions/ed082ee2-11df-4b88-96c4-9289825aecb4

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
theorem _root_.solution (A : GL (Fin N) K) :
    LinearMap.charpoly (repGL A) = (A : Matrix (Fin N) (Fin N) K).charpoly := by
  rw [repGL_eq, Matrix.charpoly_toLin']
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
