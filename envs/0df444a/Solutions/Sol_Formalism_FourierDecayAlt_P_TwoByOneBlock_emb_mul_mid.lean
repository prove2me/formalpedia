-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mul_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:16.521846+00:00
-- url     : https://prove2.me/submissions/ed6d8e46-8553-4fb3-aa17-2e3c008874be

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sum_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_col
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
theorem _root_.solution (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a : Fin (k + 1))
    (j : Fin (2 * r + k + 1)) : (embWb k r μ * M) (wI k r a) j = ∑ c, μ a c * M (wI k r c) j := by
  rw [Matrix.mul_apply, sum_mid]
  · simp only [emb_wI]
  · intro q hq
    rw [emb_out_col μ _ q hq, if_neg (show ¬ (wI k r a = q) from fun h => hq (h ▸ mid_wI a)), zero_mul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
