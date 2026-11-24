-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.borderS_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:56.383796+00:00
-- url     : https://prove2.me/submissions/181026ba-26f6-45ab-bc23-5fcde19764c9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_sgn_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_Tm_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_add_eq_sub_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_expLCS
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_qm_dropS
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
theorem _root_.solution (hLC : ExpLastCol) (hFR : ExpFirstRow) (hSk : QSkewRow) : BorderS := by
  intro A _ _ n m E e es v hE hB u
  obtain ⟨_, _, _, hvs⟩ := hB
  rw [expLCS E hLC, add_comm]
  refine add_eq_sub_of ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [qm_dropS E hFR hSk hE, Finset.sum_mul, Finset.smul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Tm_ne E _ (hvs w), Tm_ne E _ (hvs x).symm, ← zsmul_eq_mul, smul_mul_assoc, smul_smul, ← pow_add, ← neg_smul]
  congr 1
  rw [sgn_congr (b := (w : ℕ) + (x : ℕ) + 1) (by omega), pow_succ]
  ring
end Formalism.FourierDecayAlt.P.Qx6
