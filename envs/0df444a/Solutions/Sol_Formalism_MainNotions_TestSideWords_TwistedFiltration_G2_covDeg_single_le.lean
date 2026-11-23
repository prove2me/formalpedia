-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.covDeg_single_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:57.737344+00:00
-- url     : https://prove2.me/submissions/3a72bb5e-991a-4e1f-a2d4-38576ad74e03

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
theorem _root_.solution (S : Set ι) (v : ι × Fin n) : covDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
