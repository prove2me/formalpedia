-- Prove2me | solution 1 for Formalism.REAL.vanishing_outside_right_derivative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:39.24619+00:00
-- url     : https://prove2.me/submissions/d3d136bb-f2b5-4564-8631-8de07fa4f18f

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
import Theorems.Thm_Formalism_REAL_continuous_hs_real_place_taylor
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero


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
theorem _root_.solution {R : ℝ} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {X : Matrix (Fin n) (Fin n) ℂ}
    (hf : VanishesOutsideBall ε R f) (hX : inG ε X) : VanishesOutsideBall ε R (Rd X f) := by
  intro g hg hR
  unfold Rd
  have hc : ContinuousAt (fun t : ℝ => hs (g * NormedSpace.exp ((t : ℂ) • X))) 0 :=
    continuous_hs_real_place_taylor.continuousAt.comp (hasDerivAt_mul_exp_smul_zero g X).continuousAt
  have hev : ∀ᶠ t : ℝ in 𝓝 0, R < hs (g * NormedSpace.exp ((t : ℂ) • X)) :=
    hc.eventually (lt_mem_nhds (by
      show R < hs (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X)); rw [mul_exp_zero_smul_eq]; exact hR))
  have hz : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    filter_upwards [hev] with t ht
    exact hf _ (curve_mem_indefinite_unitary hg hX t) ht
  rw [hz.deriv_eq]
  simp
end Formalism.REAL
