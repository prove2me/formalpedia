-- Prove2me | solution 1 for Formalism.NG.TrivialCharacterBlockLength.length_mid_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:40.704778+00:00
-- url     : https://prove2.me/submissions/472a5737-0b5e-4c98-bf52-9b0e608f382a

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv

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
open Formalism.NG.TrivialCharacterBlockLength
variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
namespace Formalism.NG.TrivialCharacterBlockLength
theorem _root_.solution {H : Type*} [AddCommGroup H] [Module O H] (ρM : Representation O G M)
    (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  have hz : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ), z = 0 := by
    rintro ⟨z, hz⟩
    obtain ⟨-, hz2⟩ := Submodule.mem_inf.mp hz
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply] at hz2
    have h0 := hB _ hz2
    exact Subtype.ext (Subtype.ext h0)
  rw [hz a, hz b]
end Formalism.NG.TrivialCharacterBlockLength
