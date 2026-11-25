-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.hs_le_of_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:13:29.375896+00:00
-- url     : https://prove2.me/submissions/a64b0ef1-c616-4299-b7b0-cd20039e0ff6

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
theorem _root_.solution (X : Wq →L[ℂ] Wp) (A A' : Wq →L[ℂ] Wq) (K : ℝ)
    (h : ∀ v : Wq, ‖v‖ ^ 2 ≤
      K * (‖(ContinuousLinearMap.adjoint A) v‖ ^ 2 + ‖(ContinuousLinearMap.adjoint A') v‖ ^ 2)) :
    ‖B.hsVec X‖ ^ 2 ≤ K * (‖B.hsVec (X.comp A)‖ ^ 2 + ‖B.hsVec (X.comp A')‖ ^ 2) := by
  rw [hsVec_normSq_adj, hsVec_normSq_adj, hsVec_normSq_adj, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  exact h _
end Formalism.FourierDecayAlt.P.TBBx4
