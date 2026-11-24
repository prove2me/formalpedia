-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.rankOneMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:41.862804+00:00
-- url     : https://prove2.me/submissions/5a18c3ba-1142-4136-a013-660cd64e08ff

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_jV_wbPart
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mulVec_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_jV
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UHb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWb_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_UWset_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_herm_UH
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_inv_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_mul
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
theorem _root_.solution : RankOneMem := by
  intro k r z z' μsec hz hz' hsec ζ hζ h hh h' hh'
  obtain ⟨hU, hval⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  obtain ⟨η, hη, hηz, rfl⟩ := (UWset_iff hz h).1 hh
  obtain ⟨η', hη', hηz', rfl⟩ := (UWset_iff hz' h').1 hh'
  rw [emb_inv hη, ← emb_mul, ← emb_mul]
  refine ⟨(UWb_iff _).2 ⟨_, UHb_mul (UHb_mul (UHb_inv hη).2 hU') hη', rfl⟩, ?_⟩
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [emb_mulVec_jV, herm_jV, ← Matrix.mulVec_mulVec, hηz', ← Matrix.mulVec_mulVec]
  conv_lhs => rw [← inv_fix hη hηz]
  rw [herm_UH (UHb_inv hη).2, hval]
end Formalism.FourierDecayAlt.P.TwoByOneBlock
