-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:40.729146+00:00
-- url     : https://prove2.me/submissions/04a2382d-8ffc-4c9f-8251-fed656768f66

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_Wb_emb_mul


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
theorem _root_.solution {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) :
    (embWb k r μ)⁻¹ = embWb k r μ⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← emb_mul, Matrix.mul_nonsing_inv _ (UHb_inv hμ).1, emb_one]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
