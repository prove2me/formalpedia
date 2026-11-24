-- Prove2me | solution 1 for Formalism.HC.Der.smul_mem_of_inertia
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:16:44.915867+00:00
-- url     : https://prove2.me/submissions/16bc286a-debc-4b13-8043-ec4dcb8fea96

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
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
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsScalarTower ℚ E L]
namespace Formalism.HC.Der
theorem _root_.solution {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g : G) (I : Ideal S)
    (h : ∀ x : S, g • x - x ∈ I) (z : S) : g • z ∈ I ↔ z ∈ I :=
  ⟨fun hz => by simpa using I.sub_mem hz (h z), fun hz => by simpa using I.add_mem (h z) hz⟩
end Formalism.HC.Der
