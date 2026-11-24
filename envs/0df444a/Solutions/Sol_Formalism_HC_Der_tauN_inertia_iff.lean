-- Prove2me | solution 1 for Formalism.HC.Der.tauN_inertia_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:37.774465+00:00
-- url     : https://prove2.me/submissions/45398dbc-7f23-4489-923a-270718b6877a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_tauN_zO
import Theorems.Thm_Formalism_HC_Der_ringHom_ext_zO
import Theorems.Thm_Formalism_HC_Der_zO_sub_mem_iff
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
variable (N : ℕ) [NeZero N]
variable (l : ℕ) [Fact l.Prime] (Q : Ideal (𝓞 (Cond.Cyc N))) [Q.IsPrime] [Q.LiesOver (span {(l : ℤ)})]
namespace Formalism.HC.Der
theorem _root_.solution (u : (ZMod N)ˣ) :
    (∀ y : 𝓞 (Cond.Cyc N), tauN N u • y - y ∈ Q) ↔ (u : ZMod N).val ≡ 1 [MOD ordCompl[l] N] := by
  constructor
  · intro h
    have h1 : zO N ^ (u : ZMod N).val - zO N ^ 1 ∈ Q := by
      rw [pow_one, ← tauN_zO]
      exact h _
    exact (zO_sub_mem_iff N l Q _ 1).1 h1
  · intro hu y
    have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
      (Ideal.Quotient.mk Q) ?_ y
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply] at hfg
      exact Ideal.Quotient.eq.1 hfg
    · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply]
      rw [tauN_zO]
      have h1 := (zO_sub_mem_iff N l Q _ 1).2 hu
      rw [pow_one] at h1
      exact Ideal.Quotient.eq.2 h1
end Formalism.HC.Der
