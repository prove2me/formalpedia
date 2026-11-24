-- Prove2me | solution 1 for Formalism.REAL.integrable_mul_conj_of_weighted
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:12:42.506614+00:00
-- url     : https://prove2.me/submissions/2a7b3aa3-661a-451d-8e87-9861a541226d

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
import Theorems.Thm_Formalism_REAL_one_le_exponential_weight
import Theorems.Thm_Formalism_REAL_amgm_mul_le

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f')
    (h2 : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2) (muG ε))
    (h2' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2) (muG ε)) :
    Integrable (fun g : UJ ε => f (toM g) * starRingEnd ℂ (f' (toM g))) (muG ε) := by
  have hb : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2 / 2 +
      Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2 / 2) (muG ε) :=
    Integrable.add (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2 / 2)
      (g := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2 / 2)
      (Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f (toM g)‖ ^ 2)
        h2 2)
      (Integrable.div_const (f := fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖f' (toM g)‖ ^ 2)
        h2' 2)
  refine hb.mono' ((continuous_smooth_on_group_eval hf).mul ((continuous_smooth_on_group_eval hf').star)).aestronglyMeasurable
    (Eventually.of_forall fun g => ?_)
  rw [norm_mul, Complex.norm_conj]
  have he := one_le_exponential_weight ha g
  have h1 := amgm_mul_le ‖f (toM g)‖ ‖f' (toM g)‖ 1 zero_le_one
  have h3 : 0 ≤ ‖f (toM g)‖ ^ 2 := by positivity
  have h4 : 0 ≤ ‖f' (toM g)‖ ^ 2 := by positivity
  nlinarith
end Formalism.REAL
