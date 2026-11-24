-- Prove2me | solution 1 for Formalism.REAL.measurable_cutoff_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:33:36.475979+00:00
-- url     : https://prove2.me/submissions/688b56fc-96cc-4958-9a20-c61dbf46b648

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
import Theorems.Thm_Formalism_REAL_contDiff_radialCutoff
import Theorems.Thm_Formalism_REAL_continuous_frobenius_on_group


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
theorem _root_.solution (R : ℝ) : Measurable (fun g : UJ ε => radialCutoffFunction (n := n) R (toM g)) :=
  Complex.measurable_ofReal.comp ((contDiff_radialCutoff R).continuous.measurable.comp
    (Real.measurable_log.comp (continuous_frobenius_on_group ε).measurable))
end Formalism.REAL
