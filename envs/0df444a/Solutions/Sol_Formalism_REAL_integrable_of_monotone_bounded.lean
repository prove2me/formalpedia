-- Prove2me | solution 1 for Formalism.REAL.integrable_of_monotone_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:16:09.583072+00:00
-- url     : https://prove2.me/submissions/b40cd33c-97da-469d-833e-6fd21bb6bf3e

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (hF : ∀ N, Integrable (F N) μ) (hF0 : ∀ N x, 0 ≤ F N x) (hmono : ∀ x, Monotone (fun N => F N x))
    (hlim : ∀ x, ∃ N, F N x = f x) (hle : ∀ N x, F N x ≤ f x) (hf : AEStronglyMeasurable f μ)
    {B : ℝ} (hB : ∀ N, ∫ x, F N x ∂μ ≤ B) : Integrable f μ := by
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hF0 0 x).trans (hle 0 x)
  refine ⟨hf, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)]
  have hsup : ∀ x, ENNReal.ofReal (f x) = ⨆ N, ENNReal.ofReal (F N x) := by
    intro x; apply le_antisymm
    · obtain ⟨N, hN⟩ := hlim x
      rw [← hN]; exact le_iSup (fun N => ENNReal.ofReal (F N x)) N
    · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hle N x)
  rw [lintegral_congr hsup, lintegral_iSup' (fun N => (hF N).aemeasurable.ennreal_ofReal)
    (Eventually.of_forall fun x => fun N M h => ENNReal.ofReal_le_ofReal (hmono x h))]
  refine lt_of_le_of_lt (iSup_le fun N => ?_) (ENNReal.ofReal_lt_top (r := B))
  rw [← ofReal_integral_eq_lintegral_ofReal (hF N) (Eventually.of_forall (hF0 N))]
  exact ENNReal.ofReal_le_ofReal (hB N)
end Formalism.REAL
