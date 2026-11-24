-- Prove2me | solution 1 for Formalism.REAL.word_action_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:17:28.341859+00:00
-- url     : https://prove2.me/submissions/ed872ce9-4525-4868-b676-6917784d90ae

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace Formalism.REAL
theorem _root_.solution (X : Module.End ℂ (SmoothFunctionsModGroup ε)) (hX : ∀ i j, X * lieOperatorQuotient ε i j = lieOperatorQuotient ε i j * X)
    (m : SmoothFunctionsModGroup ε) : ∀ w : List (Fin n × Fin n), X (wordActionQuotient ε w m) = wordActionQuotient ε w (X m)
  | [] => rfl
  | p :: w => by
    show X (lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w m)) = lieOperatorQuotient ε p.1 p.2 (wordActionQuotient ε w (X m))
    rw [← solution X hX m w, ← Module.End.mul_apply, hX, Module.End.mul_apply]
end Formalism.REAL
