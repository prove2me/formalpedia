-- Prove2me | solution 1 for Formalism.NG.IdemLiftAlt.map_mem_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:49.211883+00:00
-- url     : https://prove2.me/submissions/014414f8-e5aa-4385-b5c8-e65fb318169f

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
theorem _root_.solution (I : Ideal O) {M N : Type*} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (φ : M →ₗ[O] N) {x : M} (hx : x ∈ I • (⊤ : Submodule O M)) :
    φ x ∈ I • (⊤ : Submodule O N) := by
  refine Submodule.smul_induction_on hx (fun r hr a _ => ?_) (fun u v hu hv => ?_)
  · rw [map_smul]; exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add]; exact Submodule.add_mem _ hu hv
end Formalism.NG.IdemLiftAlt
