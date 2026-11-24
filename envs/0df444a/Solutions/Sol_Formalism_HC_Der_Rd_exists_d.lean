-- Prove2me | solution 1 for Formalism.HC.Der.Rd.exists_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:18.692609+00:00
-- url     : https://prove2.me/submissions/058e5fc2-8c36-423f-ade2-ef9d38e40e89

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_q_ne_d
import Theorems.Thm_Formalism_HC_Der_Rd_KK_gcd
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK


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
theorem _root_.solution (C : HostCore H) : ∃ u ∈ KK H.condN (H.QS * H.q), u ∉ H.art.ker := by
  by_contra h
  push Not at h
  have hc : Nat.Coprime (H.QS * H.q) H.d := Nat.Coprime.mul_left H.QS_coprime.coprime_mul_left_right
    ((Nat.coprime_primes H.hyp.1 H.hyp.2.1).mpr (q_ne_d H))
  have h1 := KK_gcd (φ.chD.comp H.art).ker (dvd_mul_right (H.QS * H.q) H.d) (dvd_mul_left H.d (H.QS * H.q))
    (fun u hu => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.mp (h u hu), map_one])
    (fun u hu => by
      apply Units.ext
      refine (C.art_ch u).trans ?_
      rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast Int.natCast_modEq_iff.mpr (mem_KK.mp hu)), jacobiSym.one_left]
      rfl) (-1) (by rw [hc, mem_KK]; exact Nat.modEq_one)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, H.art_neg_one] at h1
  exact absurd h1 (show ¬ (-1 : ℤˣ) = 1 by decide)
end Formalism.HC.Der.Rd
