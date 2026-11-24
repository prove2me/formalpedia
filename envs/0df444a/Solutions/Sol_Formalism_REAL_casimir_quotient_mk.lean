-- Prove2me | solution 1 for Formalism.REAL.casimir_quotient_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:08.773614+00:00
-- url     : https://prove2.me/submissions/29cbf54e-5c7f-4c59-ac06-e93f8c7000c7

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
import Theorems.Thm_Formalism_REAL_lie_operator_quotient_mk
import Theorems.Thm_Formalism_REAL_finset_sum_quotient_mk
import Theorems.Thm_Formalism_REAL_coe_finset_sum_smooth

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
theorem _root_.solution (u : smoothFunctionsOnGroup ε) :
    Cas (lieOperatorQuotient ε) (quotientMkAlt u) = quotientMkAlt ⟨CasF ε u, smooth_casimir (smoothFunctions_smooth u)⟩ := by
  unfold Cas
  simp only [LinearMap.sum_apply, Module.End.mul_apply, lie_operator_quotient_mk, finset_sum_quotient_mk]
  rw [quotient_mk_eq_iff]
  intro g _
  simp only [coe_finset_sum_smooth]
  rfl
end Formalism.REAL
