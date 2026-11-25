-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.hs_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:35:05.417669+00:00
-- url     : https://prove2.me/submissions/874e508c-6dae-46b4-afc7-0497f1bfd7fb

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx4_hsVec_normSq_adj

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
theorem _root_.solution (X : Wq →L[ℂ] Wp) (A : Wq →L[ℂ] Wq) :
    ‖B.hsVec (X.comp A)‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖B.hsVec X‖ ^ 2 := by
  rw [hsVec_normSq_adj, hsVec_normSq_adj, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.adjoint.norm_map A, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
end Formalism.FourierDecayAlt.P.TBBx4
