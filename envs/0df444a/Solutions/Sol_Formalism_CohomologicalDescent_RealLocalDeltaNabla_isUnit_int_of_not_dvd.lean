-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.isUnit_int_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:11:35.778377+00:00
-- url     : https://prove2.me/submissions/35200ce3-9b34-47cb-bb27-75f2e675c77c

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.RealLocalDeltaNabla
open Formalism.GradedWeylDivisibility Formalism.UG Formalism.RankGapBounds.JumpSetsAlt Formalism.RankGapBounds.FormsTensorLocalization Formalism.CohomologicalDescent.LA Formalism.CohomologicalDescent.SL2BinomialLattices
namespace Formalism.CohomologicalDescent.RealLocalDeltaNabla
theorem _root_.solution (A : Type) [CommRing A] (l : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : A))
    (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : IsUnit (z : A) := by
  have hn : ¬ l ∣ z.natAbs := fun h => hz (Int.ofNat_dvd_left.mpr h)
  rcases Int.natAbs_eq z with h | h
  · rw [h]; simpa using hu _ hn
  · rw [h]; simpa using (hu _ hn).neg
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
