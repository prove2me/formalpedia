-- Prove2me | solution 1 for Formalism.CohomologicalDescent.RealLocalDeltaNabla.isLocalHom_of_prime_to_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:25.352401+00:00
-- url     : https://prove2.me/submissions/31154e59-4ccd-4f5b-b3b3-97ff3b6ce927

import Definitions.Def_Formalism_PieriBlockIdeals_LocalFaithfullyFlat
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Theorems.Thm_Formalism_CohomologicalDescent_RealLocalDeltaNabla_isUnit_int_of_not_dvd
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
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
theorem _root_.solution (R O : Type) [CommRing R] [CommRing O] (φ : R →+* O) (l : ℕ)
    (hlO : ¬ IsUnit (l : O)) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R))
    (hd : ∀ a : R, ∃ m : ℕ, ¬ l ∣ m ∧ ∃ z : ℤ, (m : R) * a = z) : IsLocalHom φ := by
  constructor
  intro a ha
  obtain ⟨m, hm, z, hz⟩ := hd a
  have hmO : IsUnit (m : O) := by simpa using (hu m hm).map φ
  have hzO : IsUnit (z : O) := by
    have h := congrArg φ hz
    rw [map_mul, map_natCast, map_intCast] at h
    rw [← h]; exact hmO.mul ha
  have hz' : ¬ (l : ℤ) ∣ z := by
    rintro ⟨k, rfl⟩
    apply hlO
    push_cast at hzO
    exact isUnit_of_mul_isUnit_left hzO
  have hzR : IsUnit (z : R) := isUnit_int_of_not_dvd R l hu z hz'
  rw [← hz] at hzR
  exact isUnit_of_mul_isUnit_right hzR
end Formalism.CohomologicalDescent.RealLocalDeltaNabla
