-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.mul_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:09:40.418913+00:00
-- url     : https://prove2.me/submissions/bdb45f08-37ea-42be-8f0b-23057266f258

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SpacedProductLowerBound
import Theorems.Thm_Formalism_NG_IdemLiftAlt_mul_mem_right

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
theorem _root_.solution (I : Ideal O) {i j : ℕ} {x y : A} (hx : x ∈ I ^ i • (⊤ : Submodule O A))
    (hy : y ∈ I ^ j • (⊤ : Submodule O A)) : x * y ∈ I ^ (i + j) • (⊤ : Submodule O A) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [smul_mul_assoc, pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_right _ a hy)
  · rw [add_mul]; exact Submodule.add_mem _ hu hv
end Formalism.NG.IdemLiftAlt
