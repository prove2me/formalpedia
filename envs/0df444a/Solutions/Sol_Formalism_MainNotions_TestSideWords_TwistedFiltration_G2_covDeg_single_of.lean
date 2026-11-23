-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.covDeg_single_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:57.810077+00:00
-- url     : https://prove2.me/submissions/26fa9c3a-b349-4dd9-ac31-f06c35989fc0

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
theorem _root_.solution (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    covDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
