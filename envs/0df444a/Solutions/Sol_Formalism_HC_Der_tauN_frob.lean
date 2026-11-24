-- Prove2me | solution 1 for Formalism.HC.Der.tauN_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:36.85802+00:00
-- url     : https://prove2.me/submissions/b3a26d82-b864-4e6d-ab7a-554f2f16e999

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_HC_Der_tauN_zO
import Theorems.Thm_Formalism_HC_Der_ringHom_ext_zO
import Theorems.Thm_Formalism_HC_Der_charP_quot
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
theorem _root_.solution (u : (ZMod N)ˣ) (hu : (u : ZMod N).val ≡ l [MOD ordCompl[l] N]) : IsArithFrobAt ℤ (tauN N u) Q := by
  haveI := charP_quot N l Q
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = l := by
    rw [← Ideal.LiesOver.over (P := Q) (p := span {(l : ℤ)}),
      Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  unfold IsArithFrobAt
  intro y
  rw [hcard]
  simp only [MulSemiringAction.toAlgHom_apply]
  have hfg := ringHom_ext_zO N ((Ideal.Quotient.mk Q).comp (MulSemiringAction.toRingHom _ _ (tauN N u)))
    ((frobenius (𝓞 (Cond.Cyc N) ⧸ Q) l).comp (Ideal.Quotient.mk Q)) ?_ y
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow] at hfg
    exact Ideal.Quotient.eq.1 hfg
  · simp only [RingHom.comp_apply, MulSemiringAction.toRingHom_apply, frobenius_def, ← map_pow]
    rw [tauN_zO]
    exact Ideal.Quotient.eq.2 ((zO_sub_mem_iff N l Q _ l).2 hu)
end Formalism.HC.Der
