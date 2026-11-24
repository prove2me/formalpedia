-- Prove2me | solution 1 for Formalism.REAL.lie_derivative_log_frobenius_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:44.781534+00:00
-- url     : https://prove2.me/submissions/b052ae0b-106f-45a4-a859-45f9d22265c6

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
import Theorems.Thm_Formalism_REAL_lie_derivative_real_comp_le

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
theorem _root_.solution (hl : HhLip) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    ‖Eab ε a b (fun x => ((ψ (hh x) : ℝ) : ℂ)) g‖ ≤ |deriv ψ (hh g)| * lieDerivativeLogFrobeniusBound ε a b := by
  refine (lie_derivative_real_comp_le ψ hψ (hl n ε).1 a b hg).trans ?_
  gcongr
  unfold lieDerivativeLogFrobeniusBound
  exact add_le_add ((hl n ε).2 _ g (real_part_single_mem ε a b) hg) ((hl n ε).2 _ g (imaginary_part_single_mem ε a b) hg)
end Formalism.REAL
