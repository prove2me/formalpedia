-- Prove2me | solution 1 for Formalism.REAL.signedCasimir_quotient_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:09.446131+00:00
-- url     : https://prove2.me/submissions/2b26e48f-5828-464e-9ef2-2bea097339af

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
    signedCasimirQuotient ε (quotientMkAlt u) = quotientMkAlt ⟨signedCasimirDifference ε u, smooth_signedCasimir (smoothFunctions_smooth u)⟩ := by
  unfold signedCasimirQuotient
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    lie_operator_quotient_mk, ← quotient_mk_smul, finset_sum_quotient_mk]
  rw [quotient_mk_eq_iff]
  intro g _
  simp only [coe_finset_sum_smooth, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl
end Formalism.REAL
