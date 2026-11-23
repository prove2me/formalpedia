-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.sum_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:40.372279+00:00
-- url     : https://prove2.me/submissions/c9b2068b-bddc-470d-996a-5d5c642326b5

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_blocks_disjoint
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_sum_val_eq_biUnion
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_biUnion_blocks

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
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hLi : Function.Injective L) :
    ∑ S ∈ blocks σ L, S.val = Finset.univ.val.map L := by
  rw [sum_val_eq_biUnion _ (fun S hS T hT h => blocks_disjoint hLi hS hT h), biUnion_blocks,
    Finset.image_val_of_injOn (fun a _ b _ h => hLi h)]
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
