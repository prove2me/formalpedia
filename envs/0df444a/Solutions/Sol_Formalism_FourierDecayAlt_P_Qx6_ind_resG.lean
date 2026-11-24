-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.ind_resG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:31.9948+00:00
-- url     : https://prove2.me/submissions/4495da75-51e8-4064-b661-55ee7b16315f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_wCell_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (i : Fin (r + 1)) (J : Mx k r → E) : Ind i.val (resG k r i J) := by
  intro c _ c' _ h
  funext g
  have hp : (∏ a : Fin r, (if a.val < i.val then ‖c a‖ ^ (Mdim k r a - 1) else 1 : ℝ)) =
      ∏ a : Fin r, (if a.val < i.val then ‖c' a‖ ^ (Mdim k r a - 1) else 1 : ℝ) := by
    refine Finset.prod_congr rfl (fun a _ => ?_)
    by_cases ha : a.val < i.val
    · simp [ha, h a ha]
    · simp [ha]
  simp only [resG, hp, wCell_congr h]
end Formalism.FourierDecayAlt.P.Qx6
