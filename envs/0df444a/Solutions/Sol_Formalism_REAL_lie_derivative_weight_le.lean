-- Prove2me | solution 1 for Formalism.REAL.lie_derivative_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:00:44.653371+00:00
-- url     : https://prove2.me/submissions/e3df14bf-b9f2-4682-ae56-b6289609ac84

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
import Theorems.Thm_Formalism_REAL_lie_derivative_bound_nonneg
import Theorems.Thm_Formalism_REAL_lie_derivative_log_frobenius_comp_le
import Theorems.Thm_Formalism_REAL_contDiff_weight_profile
import Theorems.Thm_Formalism_REAL_abs_deriv_weight_profile_le

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
theorem _root_.solution (hl : HhLip) {a R : ℝ} (ha : 0 ≤ a) (hR : 1 ≤ R) (i j : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ‖Eab ε i j (radialWeight a R) g‖ ≤ radialCutoff R (hh g) * Real.exp (2 * a * hh g) *
      ((2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j) := by
  refine (lie_derivative_log_frobenius_comp_le hl (weightProfileAlt a R) (contDiff_weight_profile a R) i j hg).trans ?_
  have := abs_deriv_weight_profile_le ha hR (hh g)
  calc |deriv (weightProfileAlt a R) (hh g)| * lieDerivativeLogFrobeniusBound ε i j ≤
        radialCutoff R (hh g) * Real.exp (2 * a * hh g) * (2 * cutoffDerivBound + 2 * a) * lieDerivativeLogFrobeniusBound ε i j := by
        gcongr; exact lie_derivative_bound_nonneg ε i j
    _ = _ := by ring
end Formalism.REAL
