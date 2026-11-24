-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:37:46.588208+00:00
-- url     : https://prove2.me/submissions/b94f492a-6430-4fc5-9144-63b889c6a7b9

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_out_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_out_row


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
theorem _root_.solution (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ mid k r i) : (embWb k r μ * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [emb_out_row μ i i hi, if_pos rfl, one_mul]
  · intro q _ hq; rw [emb_out_row μ i q hi, if_neg (fun h => hq h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.TwoByOneBlock
