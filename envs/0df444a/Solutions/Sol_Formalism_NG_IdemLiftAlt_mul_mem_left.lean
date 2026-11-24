-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.mul_mem_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:39.51588+00:00
-- url     : https://prove2.me/submissions/9ef38515-4232-437f-94f4-22a59d07a710

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound

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
open Formalism Formalism.NG
open Formalism.NG.IdemLiftAlt
variable {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
namespace Formalism.NG.IdemLiftAlt
theorem _root_.solution (I : Ideal O) {x : A} (y : A) (hx : x ∈ I • (⊤ : Submodule O A)) :
    x * y ∈ I • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]; exact Submodule.add_mem _ hu hv
end Formalism.NG.IdemLiftAlt
