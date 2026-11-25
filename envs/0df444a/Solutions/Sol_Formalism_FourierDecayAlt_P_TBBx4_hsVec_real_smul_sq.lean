-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.hsVec_real_smul_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:51:08.854103+00:00
-- url     : https://prove2.me/submissions/e4df13fd-b76c-4b5e-b8e6-75a7656297fa

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_hsVec_normSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.TBBx4
theorem _root_.solution (x : ℝ) (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec ((x : ℂ) • Y)‖ ^ 2 = x ^ 2 * ‖B.hsVec Y‖ ^ 2 := by
  rw [hsVec_normSq, hsVec_normSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
end Formalism.FourierDecayAlt.P.TBBx4
