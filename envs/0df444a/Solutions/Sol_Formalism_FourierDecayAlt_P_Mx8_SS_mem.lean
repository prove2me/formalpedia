-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx8.SS_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:24:11.439096+00:00
-- url     : https://prove2.me/submissions/abf22fdc-2e1c-44c9-888e-c547427d574e

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_ssScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_ops_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_mem_Cen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx8
namespace Formalism.FourierDecayAlt.P.Mx8
theorem _root_.solution (P : Par) (i : Fin P.r) (l : ℕ) : SS P l ∈ Cen P i := by
  rw [mem_Cen]
  intro g hg
  obtain ⟨w, rfl⟩ := ops_sc P i g hg
  exact (ssScalar P l w).symm
end Formalism.FourierDecayAlt.P.Mx8
