-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.mul_emb_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:59.995859+00:00
-- url     : https://prove2.me/submissions/c8455820-01f5-4d1d-b4bc-9fa56dfe5401

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sum_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_wI


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
theorem _root_.solution (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (b : Fin (k + 1)) : (M * embWb k r μ) i (wI k r b) = ∑ c, M i (wI k r c) * μ c b := by
  rw [Matrix.mul_apply, sum_mid]
  · simp only [emb_wI]
  · intro q hq
    rw [emb_out_row μ q _ hq, if_neg (show ¬ (q = wI k r b) from fun h => hq (h ▸ mid_wI b)), mul_zero]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
