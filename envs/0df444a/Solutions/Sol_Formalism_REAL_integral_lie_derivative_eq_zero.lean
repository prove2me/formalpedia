-- Prove2me | solution 1 for Formalism.REAL.integral_lie_derivative_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:19:16.943373+00:00
-- url     : https://prove2.me/submissions/2f014023-8502-4cd5-aa81-7c4a7210e2bf

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
import Theorems.Thm_Formalism_REAL_vanishing_outside_right_derivative
import Theorems.Thm_Formalism_REAL_integrable_of_vanishing_outside

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
theorem _root_.solution (hz : IntRdZero) {φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hφ : SmoothOnG ε φ) {R : ℝ}
    (hv : VanishesOutsideBall ε R φ) (a b : Fin n) :
    ∫ g : UJ ε, Eab ε a b φ (toM g) ∂(muG ε) = 0 := by
  have i1 := integrable_of_vanishing_outside (smooth_right_derivative_alt hφ (real_part_single_mem ε a b)) (vanishing_outside_right_derivative hv (real_part_single_mem ε a b))
  have i2 := integrable_of_vanishing_outside (smooth_right_derivative_alt hφ (imaginary_part_single_mem ε a b)) (vanishing_outside_right_derivative hv (imaginary_part_single_mem ε a b))
  simp only [lie_derivative_def]
  rw [integral_add i1 (i2.const_mul Complex.I), integral_const_mul,
    hz n ε φ _ R hφ (real_part_single_mem ε a b) hv, hz n ε φ _ R hφ (imaginary_part_single_mem ε a b) hv]
  ring
end Formalism.REAL
