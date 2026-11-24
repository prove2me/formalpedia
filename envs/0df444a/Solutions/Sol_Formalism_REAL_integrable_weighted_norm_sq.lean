-- Prove2me | solution 1 for Formalism.REAL.integrable_weighted_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:43.676119+00:00
-- url     : https://prove2.me/submissions/4a9b4840-2863-4309-af8c-cab61decaf21

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
import Theorems.Thm_Formalism_REAL_integrable_of_ofReal
import Theorems.Thm_Formalism_REAL_weight_mul_conj_eq
import Theorems.Thm_Formalism_REAL_integrable_weight_product

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
theorem _root_.solution (hl : HhLip) (a : ℝ) {R : ℝ} (hR : 0 < R) {v : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hv : SmoothOnG ε v) :
    Integrable (fun g : UJ ε => weightProfileAlt a R (hh (toM g)) * ‖v (toM g)‖ ^ 2) (muG ε) := by
  apply integrable_of_ofReal
  refine (integrable_weight_product hl a hR hv hv).congr (Eventually.of_forall fun g => ?_)
  exact weight_mul_conj_eq a R _ _
end Formalism.REAL
