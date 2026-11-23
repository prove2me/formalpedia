-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.repGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:36.836262+00:00
-- url     : https://prove2.me/submissions/3f249e05-76f3-43c2-9808-e974eba2ed41

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
theorem _root_.solution : Function.Injective (repGL (K := K) (N := N)) := by
  intro A B h
  apply Units.ext
  rw [repGL_eq, repGL_eq] at h
  exact Matrix.toLin'.injective h
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
