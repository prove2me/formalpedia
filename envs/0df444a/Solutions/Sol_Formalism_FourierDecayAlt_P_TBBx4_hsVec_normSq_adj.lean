-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.hsVec_normSq_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:50:07.231201+00:00
-- url     : https://prove2.me/submissions/07585999-bbbd-4942-b87c-5c6a0e332922

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
theorem _root_.solution (Y : Wq →L[ℂ] Wp) :
    ‖B.hsVec Y‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 := by
  rw [hsVec_normSq]
  calc ∑ i, ‖Y (stdOrthonormalBasis ℂ Wq i)‖ ^ 2
      = ∑ i, ∑ j, ‖inner ℂ (stdOrthonormalBasis ℂ Wp j) (Y (stdOrthonormalBasis ℂ Wq i))‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => ((stdOrthonormalBasis ℂ Wp).sum_sq_norm_inner_right _).symm
    _ = ∑ j, ∑ i, ‖inner ℂ (stdOrthonormalBasis ℂ Wq i)
          ((ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j))‖ ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ = ∑ j, ‖(ContinuousLinearMap.adjoint Y) (stdOrthonormalBasis ℂ Wp j)‖ ^ 2 :=
        Finset.sum_congr rfl fun j _ => (stdOrthonormalBasis ℂ Wq).sum_sq_norm_inner_right _
end Formalism.FourierDecayAlt.P.TBBx4
