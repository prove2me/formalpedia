-- Prove2me | solution 1 for Formalism.HC.HostRaw.mem_congrGal_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:11.036522+00:00
-- url     : https://prove2.me/submissions/8b05a9f4-d14f-4123-8639-cf05c11cfc60

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_val_modEq_one_iff
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.HC.Der
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {m : ℕ} (hm : m ∣ H.condN) (σ : H.E ≃ₐ[ℚ] H.E) :
    σ ∈ H.congrGal m ↔ ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ 1 [MOD m] ∧ H.gal σ = H.art u := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  simp only [val_modEq_one_iff hm]
  induction h using Subgroup.closure_induction with
  | mem τ hτ => simpa only [Set.mem_setOf_eq, val_modEq_one_iff hm] using hτ
  | one => exact ⟨1, map_one _, by rw [map_one, map_one]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨u, h1, h2⟩ := ha
    obtain ⟨v, h3, h4⟩ := hb
    exact ⟨u * v, by rw [map_mul, h1, h3, one_mul], by rw [map_mul, map_mul, h2, h4]⟩
  | inv a _ ha =>
    obtain ⟨u, h1, h2⟩ := ha
    exact ⟨u⁻¹, by rw [map_inv, h1, inv_one], by rw [map_inv, map_inv, h2]⟩
end Formalism.HC.HostRaw
