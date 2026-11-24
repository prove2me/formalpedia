-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:42:22.012327+00:00
-- url     : https://prove2.me/submissions/4dfa23d6-89d6-4122-8d52-7d7889528049

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_wI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_wI_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_col
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
theorem _root_.solution : embWb k r 1 = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · obtain ⟨x, rfl⟩ := mid_exists hi
      obtain ⟨y, rfl⟩ := mid_exists hj
      rw [emb_wI, Matrix.one_apply]
      simp only [wI_inj.eq_iff]
    · rw [emb_out_col _ _ _ hj]
  · rw [emb_out_row _ _ _ hi]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
