-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:35.570447+00:00
-- url     : https://prove2.me/submissions/4c574bb7-e6aa-4397-81be-336cf3d023d5

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
variable {M : Type*} [Monoid M]
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (ℓ : ℕ) (x : M) (hx : IsOfFinOrder x) :
    IsOfFinOrder (primeToPart ℓ x) := hx.pow
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
