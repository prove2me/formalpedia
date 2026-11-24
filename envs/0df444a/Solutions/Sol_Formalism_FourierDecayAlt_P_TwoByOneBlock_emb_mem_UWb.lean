-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoByOneBlock.emb_mem_UWb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:11:16.170323+00:00
-- url     : https://prove2.me/submissions/8c8a51e0-d823-49aa-9662-9520f4208f6e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_form
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_emb_fix_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_eI_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_esI_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_emb_form


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
theorem _root_.solution {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) : embWb k r μ ∈ UWb k r :=
  ⟨(emb_form μ).2 hμ, fun a => ⟨emb_fix_out μ (eI_out a), emb_fix_out μ (esI_out a)⟩⟩
end Formalism.FourierDecayAlt.P.TwoByOneBlock
