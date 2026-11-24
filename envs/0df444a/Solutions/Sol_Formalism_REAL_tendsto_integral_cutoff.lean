-- Prove2me | solution 1 for Formalism.REAL.tendsto_integral_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:51.746312+00:00
-- url     : https://prove2.me/submissions/84f28358-19ec-4ca8-8296-73f2d04928a7

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
import Theorems.Thm_Formalism_REAL_cutoff_profile_eq_one
import Theorems.Thm_Formalism_REAL_cutoff_profile_le_one
import Theorems.Thm_Formalism_REAL_cutoff_eventually_one
import Theorems.Thm_Formalism_REAL_measurable_cutoff_alt

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
theorem _root_.solution {F : UJ ε → ℂ} (hF : Integrable F (muG ε)) :
    Tendsto (fun N : ℕ => ∫ g : UJ ε, radialCutoffFunction ((N : ℝ) + 1) (toM g) * F g ∂(muG ε)) atTop
      (𝓝 (∫ g : UJ ε, F g ∂(muG ε))) := by
  refine tendsto_integral_of_dominated_convergence (fun g => ‖F g‖) (fun N => ?_) hF.norm
    (fun N => Eventually.of_forall fun g => ?_) (Eventually.of_forall fun g => ?_)
  · exact (measurable_cutoff_alt _).aestronglyMeasurable.mul hF.aestronglyMeasurable
  · rw [norm_mul]
    have h0 := cutoff_profile_eq_one (hh (toM g) / ((N : ℝ) + 1))
    have h1 := cutoff_profile_le_one (hh (toM g) / ((N : ℝ) + 1))
    have : ‖radialCutoffFunction (n := n) ((N : ℝ) + 1) (toM g)‖ ≤ 1 := by
      unfold radialCutoffFunction radialCutoff
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    calc ‖radialCutoffFunction ((N : ℝ) + 1) (toM g)‖ * ‖F g‖ ≤ 1 * ‖F g‖ := by gcongr
      _ = ‖F g‖ := one_mul _
  · obtain ⟨N, hN⟩ := cutoff_eventually_one (hh (toM g))
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun M hM => ?_⟩)
    simp [radialCutoffFunction, hN M hM]
end Formalism.REAL
