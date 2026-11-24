-- Prove2me | solution 1 for Formalism.HC.Frame.hostOrbitsPlaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:21:50.135896+00:00
-- url     : https://prove2.me/submissions/4e5c9e35-d820-4460-b24a-59cc712640dc

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrderOfSignGroupDvdTwo
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Theorems.Thm_Formalism_HC_Frame_placeOf_of_mem
import Theorems.Thm_Formalism_HC_Frame_placeOf_of_notMem
import Theorems.Thm_Formalism_HC_Frame_placeOf_snd
import Theorems.Thm_Formalism_HC_Frame_pow_mul_mem_Psi_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff
import Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
private theorem int_units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by
  intro h
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  norm_num at h'
private theorem sign_group_sq_eq_one_var (x : G0) : x ^ 2 = 1 :=
  Prod.ext (by rw [Prod.pow_fst]; exact Int.units_sq _) (by rw [Prod.pow_snd]; exact Int.units_sq _)
private theorem G0_pow_eq_ite_even (x : G0) (i : ℕ) : x ^ i = if Even i then 1 else x := by
  rcases Nat.even_or_odd i with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [if_pos ⟨k, rfl⟩, ← two_mul, pow_mul, sign_group_sq_eq_one_var, one_pow]
  · rw [if_neg (Nat.not_even_iff_odd.2 ⟨k, rfl⟩), pow_succ, pow_mul, sign_group_sq_eq_one_var, one_pow, one_mul]
private theorem not_mem_Psi_of_fst_eq_c0_or (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) :
    g ∉ φ.Psi := by
  rw [mem_Psi_iff]
  rcases hg with h | h <;> rw [h] <;> exact int_units_neg_one_ne_one
end Formalism.HC.Frame
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.Frame
open Formalism.FrobeniusOrbits
variable (φ : Frame)
namespace Formalism.HC.Frame
theorem _root_.solution (g : φ.GG) (hg : g.1 = c0 ∨ g.1 = ((1 : ℤˣ), (-1 : ℤˣ))) (τ : φ.GG) (hτ : τ ∈ φ.Psi)
    (i : ℕ) :
    (placeOf (g ^ i * τ)).2 = g.2 ^ i * τ.2 ∧
    (g.1 = c0 → (placeOf (g ^ i * τ)).1 = τ.1) ∧
    (g.1 = ((1 : ℤˣ), (-1 : ℤˣ)) →
      (placeOf (g ^ i * τ)).1 = (if Even i then 1 else φ.sg.1) * τ.1) := by
  have hg' := not_mem_Psi_of_fst_eq_c0_or φ g hg
  refine ⟨(φ.placeOf_snd _).trans rfl, fun hc => ?_, fun hs => ?_⟩
  · by_cases hi : Even i
    · rw [φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi)]
      show g.1 ^ i * τ.1 = τ.1
      rw [hc, G0_pow_eq_ite_even, if_pos hi, one_mul]
    · rw [φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h))]
      show c0 * (g.1 ^ i * τ.1) = τ.1
      rw [hc, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc, ← pow_two, sign_group_sq_eq_one_var, one_mul]
  · by_cases hi : Even i
    · rw [φ.placeOf_of_mem ((φ.pow_mul_mem_Psi_iff hg' hτ i).2 hi), if_pos hi]
      show g.1 ^ i * τ.1 = 1 * τ.1
      rw [hs, G0_pow_eq_ite_even, if_pos hi]
    · rw [φ.placeOf_of_notMem (fun h => hi ((φ.pow_mul_mem_Psi_iff hg' hτ i).1 h)), if_neg hi]
      show c0 * (g.1 ^ i * τ.1) = φ.sg.1 * τ.1
      rw [hs, G0_pow_eq_ite_even, if_neg hi, ← mul_assoc]
      congr 1
end Formalism.HC.Frame
