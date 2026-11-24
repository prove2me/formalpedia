-- Prove2me | solution 1 for Formalism.REAL.lie_derivative_real_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:17.684177+00:00
-- url     : https://prove2.me/submissions/b10534af-fc2b-437b-b6c8-f22fd08cafa4

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
import Theorems.Thm_Formalism_REAL_right_derivative_real_comp

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
    (hh : SmoothOnG ε (fun x => ((h x : ℝ) : ℂ))) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) :
    ‖Eab ε a b (fun x => ((ψ (h x) : ℝ) : ℂ)) g‖ ≤ |deriv ψ (h g)| *
      (‖Rd (cpart1 ε (Matrix.single a b 1)) (fun x => ((h x : ℝ) : ℂ)) g‖ +
        ‖Rd (cpart2 ε (Matrix.single a b 1)) (fun x => ((h x : ℝ) : ℂ)) g‖) := by
  rw [lie_derivative_def, right_derivative_real_comp ψ hψ hh (real_part_single_mem ε a b) hg, right_derivative_real_comp ψ hψ hh (imaginary_part_single_mem ε a b) hg]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul, mul_add]
  gcongr
  · exact Complex.abs_re_le_norm _
  · exact Complex.abs_re_le_norm _
end Formalism.REAL
