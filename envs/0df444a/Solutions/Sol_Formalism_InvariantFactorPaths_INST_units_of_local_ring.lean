-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.INST.units_of_local_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:05:32.311697+00:00
-- url     : https://prove2.me/submissions/c3ab13c4-0e4c-42fe-98cc-37dd7e92771f

import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SpreadSquare
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_SandwichModelProofs_Ascent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.INST
open Formalism.GradedWeylDivisibility
namespace Formalism.InvariantFactorPaths.INST
theorem _root_.solution : UnitsOfLocal := by
  unfold UnitsOfLocal PrimeToPUnits
  intro p hp O _ _ hpu c hc
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime (p : ℤ) c := by
    first
      | exact (Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr hc
      | exact (Prime.coprime_iff_not_dvd hpZ).mpr hc
      | exact Int.isCoprime_iff_gcd_eq_one.mpr
          ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr (fun h => hc (Int.natCast_dvd.mpr h)))
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (a : O) * (p : O) + (b : O) * (c : O) = 1 := by
    have h2 := congrArg (fun z : ℤ => (z : O)) hab
    push_cast at h2
    exact h2
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · exact absurd (isUnit_of_mul_isUnit_right h) hpu
  · exact isUnit_of_mul_isUnit_right h
end Formalism.InvariantFactorPaths.INST
