-- Prove2me | solution 1 for Formalism.HC.Der.discr_primes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.403373+00:00
-- url     : https://prove2.me/submissions/13902863-855b-42c6-a2c9-77a5a552ab49

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_cycRat
import Theorems.Thm_Formalism_HC_Der_Rd_dvd_discr_of_inertia
import Theorems.Thm_Formalism_HC_Der_Rd_exists_two
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
open Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (C : HostCore H) :
    (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr H.E → p ∣ H.condN) ∧ (2 : ℤ) ∣ discr H.E ∧ (H.d : ℤ) ∣ discr H.E := by
  have := H.galois
  refine ⟨fun p hp h => ?_, ?_, ?_⟩
  · have := cycRat H.condN
    let : Algebra H.E (CyclotomicField H.condN ℚ) := H.cycEmb.toRingHom.toAlgebra
    have h1 := h.trans (discr_dvd_discr H.E (CyclotomicField H.condN ℚ))
    rw [Int.natCast_dvd, IsCyclotomicExtension.Rat.natAbs_discr H.condN] at h1
    exact hp.dvd_of_dvd_pow (h1.trans (Nat.div_dvd_of_dvd (Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))))
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine dvd_discr_of_inertia Nat.prime_two fun P _ _ => ?_
    obtain ⟨u, hu, h1⟩ := exists_two H
    refine ⟨H.gal.symm (H.art u), fun h2 => h1 (H.gal.symm.map_eq_one_iff.mp h2), ?_⟩
    exact (C.inertia 2 P _).mpr ⟨u, mem_KK.mp hu, H.gal.apply_symm_apply _⟩
  · refine dvd_discr_of_inertia H.hyp.2.1 fun P _ _ => ⟨H.gal.symm φ.iod, fun h2 => ?_,
      (C.inertia_d P _).mpr (Or.inr (H.gal.apply_symm_apply _))⟩
    exact absurd (congrArg (fun g : φ.GG => g.1) (H.gal.symm.map_eq_one_iff.mp h2))
      (show ¬ ((1, -1) : G0) = 1 by decide)
end Formalism.HC.Der
