-- Prove2me | solution 1 for Formalism.REAL.right_derivative_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:18:05.830656+00:00
-- url     : https://prove2.me/submissions/fa38081d-1ecd-46f3-a025-553269de3267

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
import Theorems.Thm_Formalism_REAL_mul_exp_zero_smul_eq
import Theorems.Thm_Formalism_REAL_hasDerivAt_smooth_curve

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
theorem _root_.solution {f h : Matrix (Fin n) (Fin n) ℂ → ℂ} {g X : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hh : SmoothOnG ε h) (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => f x * h x) g = Rd X f g * h g + f g * Rd X h g := by
  have H := (hasDerivAt_smooth_curve hf hX hg).mul (hasDerivAt_smooth_curve hh hX hg)
  rw [mul_exp_zero_smul_eq] at H
  exact H.deriv
end Formalism.REAL
