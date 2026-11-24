-- Prove2me | solution 1 for Formalism.REAL.isCompact_frobenius_ball_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:17:29.9498+00:00
-- url     : https://prove2.me/submissions/38949b8f-8f2f-4e40-bd61-3a135f9cd2df

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
import Theorems.Thm_Formalism_REAL_hermitian_small_ball
import Theorems.Thm_Formalism_REAL_isClosedEmbeddingMatrix


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
theorem _root_.solution (ε : Fin n → Bool) (R : ℝ) : IsCompact {g : UJ ε | hsG g ≤ R} := by
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 R)
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
end Formalism.REAL
