-- Prove2me | solution 1 for Formalism.REAL.lie_derivative_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:04.381991+00:00
-- url     : https://prove2.me/submissions/e6fdbea9-c950-4e51-8e29-fdb178fa9141

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
import Theorems.Thm_Formalism_REAL_right_derivative_conj
import Theorems.Thm_Formalism_REAL_signature_sign_mul_self
import Theorems.Thm_Formalism_REAL_lie_derivative_swap

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
    Eab ε a b (fun x => starRingEnd ℂ (f x)) g =
      -((sgn ε a b : ℝ) : ℂ) * starRingEnd ℂ (Eab ε b a f g) := by
  rw [lie_derivative_swap a b hf hg, lie_derivative_def, right_derivative_conj hf (real_part_single_mem ε a b) hg,
    right_derivative_conj hf (imaginary_part_single_mem ε a b) hg]
  have hs := signature_sign_mul_self ε a b
  simp only [map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (starRingEnd ℂ (Rd (cpart1 ε (Matrix.single a b 1)) f g) +
    Complex.I * starRingEnd ℂ (Rd (cpart2 ε (Matrix.single a b 1)) f g)) * (-hs)
end Formalism.REAL
