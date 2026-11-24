-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.maxTwistDegree_pderiv_le_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:58:53.359735+00:00
-- url     : https://prove2.me/submissions/100c4d76-8e7f-4916-9220-80f9b8520b88

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_divDer_single_one
import Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_vecDeg_zero__7e0841f8945e
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_covDeg_single_le
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_lam1S


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
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
theorem _root_.solution (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1
    (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
