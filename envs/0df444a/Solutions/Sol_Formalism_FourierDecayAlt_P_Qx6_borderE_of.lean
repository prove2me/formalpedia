-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.borderE_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:24:47.915635+00:00
-- url     : https://prove2.me/submissions/43202b3c-c17b-4f91-9a56-22bc9297f49b

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Tm_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_add_eq_sub_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expFCE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_dropE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (hFC : ExpFirstCol) (hLR : ExpLastRow) (hSk : QSkewRow) : BorderE := by
  intro A _ _ n m E e es v hE hB u
  obtain ⟨_, _, hve, _⟩ := hB
  rw [expFCE E hFC]
  refine add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [qm_dropE E hLR hSk hE, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Tm_ne E _ (hve w), Tm_ne E _ (hve x).symm, ← zsmul_eq_mul, mul_smul_comm, smul_smul, ← pow_add, ← neg_smul,
    show u - 1 - 1 = u - 2 by ring, mul_assoc]
  congr 1
  rw [show (w : ℕ) + 1 + (x : ℕ) = (w : ℕ) + (x : ℕ) + 1 by ring, pow_succ]
  ring
end Formalism.FourierDecayAlt.P.Qx6
