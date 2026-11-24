-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.injective_of_prime_to_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:15.137098+00:00
-- url     : https://prove2.me/submissions/b18d2521-3c93-4d62-981c-fef360e37afc

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
theorem _root_.solution (R O : Type) [CommRing R] [CommRing O] [CharZero O] (φ : R →+* O) (l : ℕ)
    (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨m, hm, z, hz⟩ := hd a
  have h1 : ((z : ℤ) : O) = 0 := by
    have h := congrArg φ hz
    rw [map_mul, ha, mul_zero, map_intCast] at h
    exact h.symm
  have hz0 : z = 0 := Int.cast_eq_zero.mp h1
  have hma : (m : R) * a = 0 := by rw [hz, hz0, Int.cast_zero]
  exact (hu m hm).mul_right_eq_zero.mp hma
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
