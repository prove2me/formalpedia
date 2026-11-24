-- Prove2me | solution 1 for Formalism.HC.CharData.muPM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:35:09.139716+00:00
-- url     : https://prove2.me/submissions/b76e1c24-7175-4d67-9bd4-e51d25884328

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_z_spec
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.CharData
variable {φ : Frame} (D : CharData φ)
namespace Formalism.HC.CharData
theorem _root_.solution (h : ∀ k : ℕ, k ∣ D.QS * D.q * D.d →
    (∀ u : (ZMod (D.QS * D.q * D.d))ˣ, D.art u = 1 → (u : ZMod (D.QS * D.q * D.d)).val ≡ 1 [MOD k]) → k ∣ 2) :
    D.toHostRaw.MuPM := by
  have hz := Cond.z_spec (D.QS * D.q * D.d)
  have key : ∀ y : D.E, (y : D.L) ^ (D.QS * D.q * D.d) = 1 → y = 1 ∨ y = -1 := by
    intro y hy
    have h2 : orderOf (y : D.L) ∣ 2 := by
      refine h _ (orderOf_dvd_of_pow_eq_one hy) fun u hu => ?_
      have hfin : IsOfFinOrder (y : D.L) := isOfFinOrder_iff_pow_eq_one.2 ⟨_, Nat.pos_of_ne_zero (NeZero.ne _), hy⟩
      have h1 := (mem_fixedField_iff _ _).mp y.2 (D.cyc.symm u)
        (by rw [MonoidHom.mem_ker, res_apply, MulEquiv.apply_symm_apply, hu])
      rw [D.cyc_apply _ _ hy, MulEquiv.apply_symm_apply] at h1
      exact hfin.pow_eq_pow_iff_modEq.mp (h1.trans (pow_one _).symm)
    have h3 : (y : D.L) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
    have h4 : y ^ 2 = 1 := Subtype.ext (by push_cast; exact h3)
    exact sq_eq_one_iff.mp h4
  rintro (x : D.E) ⟨m, hm, hx⟩
  have hfin : IsOfFinOrder (x : D.L) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, congrArg (fun t : D.E => (t : D.L)) hx⟩
  have hprim : IsPrimitiveRoot (x : D.L) (orderOf (x : D.L)) := IsPrimitiveRoot.orderOf _
  have hdvd := hprim.dvd_of_isCyclotomicExtension (D.QS * D.q * D.d) (orderOf_pos_iff.2 hfin).ne'
  have h2 := key (x ^ 2) (by
    have h3 : (x : D.L) ^ (2 * (D.QS * D.q * D.d)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
    rw [pow_mul] at h3
    exact h3)
  rcases h2 with h2 | h2
  · exact sq_eq_one_iff.mp h2
  · refine key x ?_
    have h4 : x ^ 2 ^ 2 = 1 := by rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, h2]; simp
    have h5 : (x : D.L) ^ 2 ^ 2 = 1 := congrArg (fun t : D.E => (t : D.L)) h4
    have hc : 2 ^ 2 ∣ D.QS * D.q * D.d :=
      (((pow_dvd_pow 2 (by omega)).trans D.tower_dvd).mul_right _).mul_right _
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one h5).trans hc)
end Formalism.HC.CharData
