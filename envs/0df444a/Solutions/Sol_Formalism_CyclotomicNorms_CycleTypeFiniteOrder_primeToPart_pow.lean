-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.primeToPart_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:36.267653+00:00
-- url     : https://prove2.me/submissions/ba7a8fa0-50b3-4706-86c2-94c338da3368

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
theorem _root_.solution (ℓ : ℕ) (x : M) (k : ℕ) (h : orderOf (x ^ k) = orderOf x) :
    primeToPart ℓ (x ^ k) = primeToPart ℓ x ^ k := by
  unfold primeToPart
  rw [h, ← pow_mul, ← pow_mul, mul_comm k]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
