-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G1.flt_tay_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:09.904586+00:00
-- url     : https://prove2.me/submissions/bb4a7c8e-ec6f-47b9-b6da-f0ff1974b69f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_AlmostEverywhereSpherical
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_tay_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
open Formalism.MainNotions.G
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
theorem _root_.solution (R : Type*) [CommRing R] {σ : Type*} (F : MvPolynomial σ R) (be : σ →₀ ℕ) :
    coeff be (flt_tay R σ F) = divDer be F := by
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, divDer]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [show monomial m (coeff m F) = C (coeff m F) * monomial m 1 by rw [C_mul_monomial, mul_one], map_mul]
  have hC : flt_tay R σ (C (coeff m F)) = C (C (coeff m F)) := by simp [flt_tay]
  rw [hC, coeff_C_mul, flt_tay_monomial, flt_g, C_mul_monomial]
  split_ifs with hle
  · rfl
  · have hz : (be.prod fun k j => (m k).choose j) = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, m k < be k := by
        by_contra hcon
        push_neg at hcon
        exact hle fun k => hcon k
      rw [Finsupp.prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 (by omega)) (Nat.choose_eq_zero_of_lt hk)
    rw [hz, Nat.cast_zero, mul_zero, monomial_zero]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
