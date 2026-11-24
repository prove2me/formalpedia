-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.valS_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:05.486275+00:00
-- url     : https://prove2.me/submissions/e9bcecd7-04f3-4b90-9125-3246a952168b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_divDer_zero__c709542f8f89
import Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_vecDeg_zero__7e0841f8945e
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_covDeg_single_le
import Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G2_X_eq_monomial__aa92a785880b
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_op_valS


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
    valS LL S F ≤ valS LL S (X v * F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 1
    (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
