-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:00.01931+00:00
-- url     : https://prove2.me/submissions/4defe104-dd5d-4be0-93b6-2d0d1ef1cb0f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mid_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_col
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (embWb k r μ)ᴴ = embWb k r μᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · obtain ⟨x, rfl⟩ := mid_exists hi
      obtain ⟨y, rfl⟩ := mid_exists hj
      rw [emb_wI, emb_wI, Matrix.conjTranspose_apply]
    · rw [emb_out_row _ _ _ hj, emb_out_col _ _ _ hj]
      by_cases h : i = j
      · rw [if_pos h.symm, if_pos h, star_one]
      · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]
  · rw [emb_out_col _ _ _ hi, emb_out_row _ _ _ hi]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h, star_one]
    · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
