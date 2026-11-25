-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.equiv_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:42:04.181746+00:00
-- url     : https://prove2.me/submissions/0bbae801-ee4f-42bb-bc38-8accf6cba0fd

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_cellDecomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_equivDet_of_cellDecomp


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
theorem _root_.solution : Formalism.FourierDecayAlt.JF.EquivDet := jf_equivDet_of_cellDecomp BigCellDiagonalMap.cellDecomp
end Formalism.FourierDecayAlt.P
