-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.units_of_local_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:13:17.939151+00:00
-- url     : https://prove2.me/submissions/2f087a39-82d5-477c-98ee-03208be28405

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution : UnitsOfLocal := by
  intro O _ _ l hl hlO m hm
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  have hb : ((l : ℤ) * Nat.gcdA l m + (m : ℤ) * Nat.gcdB l m) = 1 := by
    have h := Nat.gcd_eq_gcd_ab l m
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    exact h.symm
  have hO : ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) = 1 := by
    have h := congrArg (Int.cast : ℤ → O) hb
    push_cast at h
    exact h
  have hu : IsUnit ((l : O) * (Nat.gcdA l m : O) + (m : O) * (Nat.gcdB l m : O)) := by
    rw [hO]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
  · exact absurd (isUnit_of_mul_isUnit_left h) hlO
  · exact isUnit_of_mul_isUnit_left h
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
