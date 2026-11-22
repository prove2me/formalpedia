-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.twistSub_X_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:24.539819+00:00
-- url     : https://prove2.me/submissions/8de1aa4c-f332-4f9c-9ee4-cf280d073ab5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne

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
theorem _root_.solution (j : Fin n) (v : ι × Fin n) (h : v.1 ∉ S) :
    twistSub (R := R) LL S j (X v) = X v := by
  simp [twistSub, h]
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
