-- Prove2me | solution 1 for Formalism.HC.Der.Rd.exists_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:19.536802+00:00
-- url     : https://prove2.me/submissions/adedf01c-27fa-477a-bac6-2e42257fcbbb

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_hcl_eq_one
import Theorems.Thm_Formalism_HC_Der_Rd_hH_art
import Theorems.Thm_Formalism_HC_Der_Rd_KK_gcd
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : ∃ u ∈ KK H.condN (ordCompl[2] H.condN), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (ordCompl[2] H.condN) (2 ^ (φ.e + 2)) :=
    ((Nat.coprime_ordCompl Nat.prime_two (NeZero.ne _)).pow_left _).symm
  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (two_dvd H)
    (ZMod.unitOfCoprime 3 (Nat.Coprime.pow_right _ (by norm_num)))
  have h1 := KK_gcd (φ.hH.comp ((MonoidHom.snd _ _).comp H.art)).ker (Nat.ordCompl_dvd _ 2) (two_dvd H)
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one, map_one])
    (fun u hu => by
      refine (hH_art H u).trans ?_
      rw [MonoidHom.mem_ker.mp ((mem_ker_iff (two_dvd H) u).mpr (mem_KK.mp hu))]
      rfl) u (by rw [hc, mem_KK]; exact Nat.modEq_one)
  have h2 := (hH_art H u).symm.trans h1
  rw [hu] at h2
  have h3 : 2 ^ 4 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by have := H.two_le_e; omega)
  rcases hcl_eq_one h2 with h4 | h4
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_one] at h5
    have h6 : ((2 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega
  · have h5 := congrArg Units.val h4
    rw [ZMod.coe_unitOfCoprime, Units.val_neg, Units.val_one] at h5
    have h6 : ((4 : ℕ) : ZMod (2 ^ (φ.e + 2))) = 0 := by
      push_cast at h5 ⊢
      linear_combination h5
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).mp h6)
    omega
end Formalism.HC.Der.Rd
