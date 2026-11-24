-- Prove2me | solution 1 for Formalism.HC.HostRaw.art_eq_one_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:16:04.772257+00:00
-- url     : https://prove2.me/submissions/c6ec876e-0b89-4516-a869-81cb1138f939

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_CycImage
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
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
theorem _root_.solution (u : (ZMod H.condN)ˣ) (hu : (u : ZMod H.condN).val ≡ 1 [MOD H.condN]) : H.art u = 1 := by
  have h1 : u = 1 := by
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (u : ZMod H.condN), (ZMod.natCast_eq_natCast_iff _ _ _).2 hu]
    simp
  rw [h1, map_one]
end Formalism.HC.HostRaw
