-- Prove2me | solution 1 for Formalism.REAL.right_derivative_real_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:00:12.709012+00:00
-- url     : https://prove2.me/submissions/4f839ea5-40cb-414f-99df-eef71990af6f

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
theorem _root_.solution {h : Matrix (Fin n) (Fin n) ℂ → ℝ} (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) :
    Rd X (fun x => ((ψ (h x) : ℝ) : ℂ)) g =
      ((deriv ψ (h g) * (Rd X (fun x => ((h x : ℝ) : ℂ)) g).re : ℝ) : ℂ) := by
  have D := hasDerivAt_smooth_curve hh hX hg
  have D2 : HasDerivAt (fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X)))
      (Rd X (fun x => ((h x : ℝ) : ℂ)) g).re 0 := by
    have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) D
    have e : (⇑Complex.reCLM ∘ fun t : ℝ => ((h (g * NormedSpace.exp ((t : ℂ) • X)) : ℝ) : ℂ)) =
        fun t : ℝ => h (g * NormedSpace.exp ((t : ℂ) • X)) := by
      funext t; simp
    rw [e, Complex.reCLM_apply] at this
    exact this
  have hd : DifferentiableAt ℝ ψ (h g) := hψ.differentiable (by simp) _
  have D3 := hd.hasDerivAt.comp_of_eq (0 : ℝ) D2 (by rw [mul_exp_zero_smul_eq])
  exact D3.ofReal_comp.deriv
end Formalism.REAL
