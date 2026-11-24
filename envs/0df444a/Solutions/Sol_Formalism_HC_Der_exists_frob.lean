-- Prove2me | solution 1 for Formalism.HC.Der.exists_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:33:00.145412+00:00
-- url     : https://prove2.me/submissions/437d5da6-628a-4bc6-8e9c-81543981a492

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_exists_unit_modEq
import Theorems.Thm_Formalism_HC_Der_frob_of_modEq
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
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})] :
    ∃ (F : H.E ≃ₐ[ℚ] H.E) (w : (ZMod H.condN)ˣ), IsArithFrobAt ℤ F P ∧
      (w : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧ H.gal F = H.art w := by
  have hl : l.Prime := Fact.out
  have hcop : l.Coprime (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl (NeZero.ne _)
  obtain ⟨w, hw⟩ := exists_unit_modEq (Nat.ordCompl_dvd H.condN l) l hcop
  exact ⟨H.gal.symm (H.art w), w, frob_of_modEq H l P _ w hw (by simp), hw, by simp⟩
end Formalism.HC.Der
