-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mulVec_jV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:42:17.061882+00:00
-- url     : https://prove2.me/submissions/22283f40-bec3-4f6c-866e-cb657c3907be

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_sum_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_out
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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    embWb k r μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  funext i
  show ∑ j, embWb k r μ i j * jV k r u j = _
  rw [sum_mid _ (fun j hj => by rw [jV_out u hj, mul_zero])]
  by_cases hi : mid k r i
  · obtain ⟨a, rfl⟩ := mid_exists hi
    simp only [emb_wI, jV_wI]
    rfl
  · rw [jV_out _ hi]
    apply Finset.sum_eq_zero
    intro b _
    rw [emb_out_row μ i _ hi, if_neg (show ¬ (i = wI k r b) from fun h => hi (h ▸ mid_wI b)), zero_mul]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
