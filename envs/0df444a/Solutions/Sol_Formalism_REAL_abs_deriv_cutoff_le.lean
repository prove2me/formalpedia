-- Prove2me | solution 1 for Formalism.REAL.abs_deriv_cutoff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:38:54.840145+00:00
-- url     : https://prove2.me/submissions/fd72547c-3fe5-4e02-bbc3-20c7b04857a3

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
import Theorems.Thm_Formalism_REAL_abs_deriv_cutoff_profile_le
import Theorems.Thm_Formalism_REAL_hasDerivAt_cutoff_alt

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
namespace Formalism.REAL
theorem _root_.solution {R : ℝ} (hR : 0 < R) (t : ℝ) : |deriv (radialCutoff R) t| ≤ cutoffDerivBound / R := by
  rw [(hasDerivAt_cutoff_alt R t).deriv, abs_mul, abs_of_pos (by positivity : 0 < 1 / R)]
  have := abs_deriv_cutoff_profile_le (t / R)
  calc |deriv cutoffProfile (t / R)| * (1 / R) ≤ cutoffDerivBound * (1 / R) := by gcongr
    _ = cutoffDerivBound / R := by ring
end Formalism.REAL
