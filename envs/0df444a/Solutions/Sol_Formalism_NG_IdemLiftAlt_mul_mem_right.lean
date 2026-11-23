-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.mul_mem_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:49.244049+00:00
-- url     : https://prove2.me/submissions/fafd9033-e80e-4538-9dbd-4ce6f83fb52f

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
theorem _root_.solution (I : Ideal O) (y : A) {x : A} (hx : x ∈ I • (⊤ : Submodule O A)) :
    y * x ∈ I • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]; exact Submodule.add_mem _ hu hv
end Formalism.NG.IdemLiftAlt
