-- Prove2me | solution 1 for Formalism.HC.Der.tauN_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:17:59.275587+00:00
-- url     : https://prove2.me/submissions/80b9ad24-12d6-4ccd-9e12-d11211b9e2c2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_tauN_root
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
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable (N : ℕ) [NeZero N]
namespace Formalism.HC.Der
theorem _root_.solution (Ψ : Cond.Cyc N →+* ℂ) (x : Cond.Cyc N) : Ψ (tauN N (-1) x) = starRingEnd ℂ (Ψ x) := by
  have key : (Ψ.comp (tauN N (-1) : Cond.Cyc N →+* Cond.Cyc N)).toRatAlgHom =
      ((starRingEnd ℂ).comp Ψ).toRatAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top
      (IsCyclotomicExtension.adjoin_primitive_root_eq_top (Cond.z_spec N)) ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show Ψ (tauN N (-1) (Cond.z N)) = starRingEnd ℂ (Ψ (Cond.z N))
    have hz := (Cond.z_spec N).pow_eq_one
    have h1 : ‖Ψ (Cond.z N)‖ = 1 :=
      Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) (NeZero.ne N)
    have h2 : Cond.z N ^ ((-1 : (ZMod N)ˣ) : ZMod N).val * Cond.z N = 1 := by
      rw [← pow_succ, (Cond.z_spec N).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [ZMod.natCast_zmod_val]
      simp
    rw [tauN_root N _ _ hz, ← Complex.inv_eq_conj h1]
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, h2, map_one]
  exact DFunLike.congr_fun key x
end Formalism.HC.Der
