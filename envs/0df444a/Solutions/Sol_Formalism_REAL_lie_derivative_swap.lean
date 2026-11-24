-- Prove2me | solution 1 for Formalism.REAL.lie_derivative_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:10.32957+00:00
-- url     : https://prove2.me/submissions/9bd113a2-bae6-47fd-98de-931cd793b44f

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
import Theorems.Thm_Formalism_REAL_real_part_single_swap
import Theorems.Thm_Formalism_REAL_imaginary_part_single_swap
import Theorems.Thm_Formalism_REAL_right_derivative_linear


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
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Eab ε b a f g = -((sgn ε a b : ℝ) : ℂ) * Rd (cpart1 ε (Matrix.single a b 1)) f g +
      Complex.I * (((sgn ε a b : ℝ) : ℂ) * Rd (cpart2 ε (Matrix.single a b 1)) f g) := by
  rw [lie_derivative_def, real_part_single_swap, imaginary_part_single_swap,
    (right_derivative_linear n ε f f _ _ (-(sgn ε a b)) 0 g hf hf (real_part_single_mem ε a b) (real_part_single_mem ε a b) hg).2.1,
    (right_derivative_linear n ε f f _ _ (sgn ε a b) 0 g hf hf (imaginary_part_single_mem ε a b) (imaginary_part_single_mem ε a b) hg).2.1]
  push_cast; ring
end Formalism.REAL
