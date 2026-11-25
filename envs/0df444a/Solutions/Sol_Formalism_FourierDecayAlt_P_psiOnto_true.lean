-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.psiOnto_true
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:29.551797+00:00
-- url     : https://prove2.me/submissions/c3901e0d-0123-4056-bcaa-966ca5a6ac2d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_cellDecomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_psiOnto_of_cellDecomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.PsiOnto := jf_psiOnto_of_cellDecomp BigCellDiagonalMap.cellDecomp
end Formalism.FourierDecayAlt.P
