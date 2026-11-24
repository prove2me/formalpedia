-- Prove2me | solution 1 for Formalism.NG.KernelLengthBounds.length_ker_smul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:09:23.634794+00:00
-- url     : https://prove2.me/submissions/c3fa9b17-601f-423e-8433-ba34483f7878

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockRhoCount
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Theorems.Thm_Formalism_NG_KernelLengthBounds_length_ker_smul_pi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.KernelLengthBounds
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.KernelLengthBounds
theorem _root_.solution (a : O) :
    Module.length O (LinearMap.ker (DistribSMul.toLinearMap O (KO O) a)) ≤
      IsDiscreteValuationRing.addVal O a := by
  have h := length_ker_smul_pi (O := O) Unit a
  have e : ↥(LinearMap.ker (DistribSMul.toLinearMap O (Unit → KO O) a)) ≃ₗ[O]
      ↥(LinearMap.ker (DistribSMul.toLinearMap O (KO O) a)) :=
    LinearEquiv.ofSubmodules (LinearEquiv.funUnique Unit O (KO O)) _ _ (by
      ext x
      simp only [Submodule.mem_map_equiv, LinearMap.mem_ker, DistribSMul.toLinearMap_apply]
      constructor
      · intro hx
        simpa using congrFun hx ()
      · intro hx
        funext i
        simpa using hx)
  rw [← e.length_eq, h]
  simp
end Formalism.NG.KernelLengthBounds
