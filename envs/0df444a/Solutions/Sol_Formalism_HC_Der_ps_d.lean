-- Prove2me | solution 1 for Formalism.HC.Der.ps_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:19:43.733539+00:00
-- url     : https://prove2.me/submissions/70baf2a1-5287-43ac-a806-ec370fef0d95

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Theorems.Thm_Formalism_HC_Der_sq_mod
import Theorems.Thm_Formalism_HC_Der_cop_QSq_d
import Theorems.Thm_Formalism_HC_Der_split_QSq
import Theorems.Thm_Formalism_HC_Der_ps_congr
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Der_val_modEq_iff
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
theorem _root_.solution : ∀ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ H.d [MOD H.QS * H.q] → (H.art u).1.1 = -1 := by
  intro u hu
  have hM0 : H.QS * H.q ≠ 0 := Nat.mul_ne_zero H.QS_pos.ne' H.hyp.1.ne_zero
  haveI : NeZero (H.QS * H.q) := ⟨hM0⟩
  have hd8 : (H.d : ℤ) % 8 = 7 := by have := H.hyp.2.2.2.1; omega
  obtain ⟨s, hs⟩ := sq_mod hd8 (H.QS * H.q) hM0 (split_QSq H)
  have hs' : ((s : ZMod (H.QS * H.q))) ^ 2 = -((H.d : ℕ) : ZMod (H.QS * H.q)) := by
    have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hs
    push_cast at h0
    linear_combination h0
  have hdu : IsUnit ((H.d : ℕ) : ZMod (H.QS * H.q)) :=
    (ZMod.unitOfCoprime H.d (cop_QSq_d H).symm).isUnit
  have hsu : IsUnit ((s : ZMod (H.QS * H.q))) := by
    have h0 : IsUnit ((s : ZMod (H.QS * H.q)) ^ 2) := by rw [hs']; exact hdu.neg
    exact (isUnit_pow_iff two_ne_zero).mp h0
  obtain ⟨w, hw⟩ := ZMod.unitsMap_surjective (QSq_dvd H) hsu.unit
  have hneg : ((ZMod.unitsMap (QSq_dvd H) (-1) : (ZMod (H.QS * H.q))ˣ) : ZMod (H.QS * H.q)) = -1 := by
    simp [ZMod.unitsMap]
  have key : ZMod.unitsMap (QSq_dvd H) u = ZMod.unitsMap (QSq_dvd H) (-1 * w ^ 2) := by
    apply Units.ext
    rw [(val_modEq_iff (QSq_dvd H) u H.d).mp hu, map_mul, map_pow, hw, Units.val_mul,
      Units.val_pow_eq_pow_val, IsUnit.unit_spec, hs', hneg]
    ring
  have h1 := ps_congr H u (-1 * w ^ 2) key
  rw [h1, map_mul, map_pow, H.art_neg_one, Prod.fst_mul, Prod.fst_mul, Prod.pow_fst, Prod.pow_fst,
    Int.units_sq, mul_one]
  rfl
end Formalism.HC.Der
