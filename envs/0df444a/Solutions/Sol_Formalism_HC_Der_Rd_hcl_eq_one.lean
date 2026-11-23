-- Prove2me | solution 1 for Formalism.HC.Der.Rd.hcl_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:46.292419+00:00
-- url     : https://prove2.me/submissions/2ecb6a00-21fc-4617-8bf0-5a2690d38175

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
namespace Formalism.HC.Der.Rd
theorem _root_.solution {e : ℕ} {v : (ZMod (2 ^ (e + 2)))ˣ} (h : hcl e v = 1) : v = 1 ∨ v = -1 := by
  unfold hcl at h
  rw [QuotientGroup.eq_one_iff] at h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [← hk, ← two_mul, zpow_mul]
    simp
  · right
    rw [← hk, zpow_add, zpow_mul]
    simp
end Formalism.HC.Der.Rd
