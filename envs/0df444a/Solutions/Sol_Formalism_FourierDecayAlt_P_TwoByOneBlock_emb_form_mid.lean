-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_form_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:35:12.049395+00:00
-- url     : https://prove2.me/submissions/0ca56085-f725-45d1-825b-95f637ceea8a

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_mul_emb_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_Hpk_wI
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_conjTranspose

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
theorem _root_.solution (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a b : Fin (k + 1)) :
    ((embWb k r μ)ᴴ * Hpk k r * embWb k r μ) (wI k r a) (wI k r b) = (μᴴ * Hb k * μ) a b := by
  rw [emb_conjTranspose, mul_emb_mid, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [emb_mul_mid, Matrix.mul_apply]
  simp only [Hpk_wI]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
