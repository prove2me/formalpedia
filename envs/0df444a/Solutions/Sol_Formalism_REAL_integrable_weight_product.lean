-- Prove2me | solution 1 for Formalism.REAL.integrable_weight_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:16.115334+00:00
-- url     : https://prove2.me/submissions/e93ff408-1dd6-4747-b8f2-798331c9de5f

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
import Theorems.Thm_Formalism_REAL_smooth_on_group_conj
import Theorems.Thm_Formalism_REAL_vanishing_outside_mul_left
import Theorems.Thm_Formalism_REAL_integrable_of_vanishing_outside
import Theorems.Thm_Formalism_REAL_smooth_weight
import Theorems.Thm_Formalism_REAL_weight_vanishing_outside

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
theorem _root_.solution (hl : HhLip) (a : ℝ) {R : ℝ} (hR : 0 < R) {u h : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hu : SmoothOnG ε u) (hh' : SmoothOnG ε h) :
    Integrable (fun g : UJ ε => radialWeight a R (toM g) * u (toM g) * starRingEnd ℂ (h (toM g)))
      (muG ε) :=
  integrable_of_vanishing_outside (f := fun x => radialWeight a R x * u x * starRingEnd ℂ (h x))
    (smooth_on_group_mul (smooth_on_group_mul (smooth_weight hl a R) hu) (smooth_on_group_conj hh'))
    (vanishing_outside_mul_left _ (vanishing_outside_mul_left _ (weight_vanishing_outside a hR)))
end Formalism.REAL
