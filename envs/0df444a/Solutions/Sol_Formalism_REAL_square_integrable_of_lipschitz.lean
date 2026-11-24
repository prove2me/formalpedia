-- Prove2me | solution 1 for Formalism.REAL.square_integrable_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:19.492941+00:00
-- url     : https://prove2.me/submissions/9196f100-5df0-4bf7-a321-c46cb8984555

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
import Theorems.Thm_Formalism_REAL_integrable_lie_derivative_pairing
import Theorems.Thm_Formalism_REAL_weighted_square_integrable_filtration

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
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) : SmoothVectorGrowthBound := by
  intro n ε W c a _ ha hsm hstab hcas hint w₁ w₂ f f' hf hf'
  have P : ∀ (w : List (Fin n × Fin n)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), f ∈ W →
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w f (toM g)‖ ^ 2)
        (muG ε) :=
    fun w f hf => weighted_square_integrable_filtration hl hz ha hsm hstab hcas hint w.length w le_rfl f hf
  refine ⟨smooth_iterated_lie_derivative (hsm f hf) w₁, P w₁ f hf, fun i j => ?_⟩
  exact integrable_lie_derivative_pairing hl hz ha (smooth_iterated_lie_derivative (hsm f hf) w₁) (smooth_iterated_lie_derivative (hsm f' hf') w₂)
    (P w₁ f hf) (P w₂ f' hf') i j (P ((i, j) :: w₁) f hf) (P ((j, i) :: w₂) f' hf')
end Formalism.REAL
