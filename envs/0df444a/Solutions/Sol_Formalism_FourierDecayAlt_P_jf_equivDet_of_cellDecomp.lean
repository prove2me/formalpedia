-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.jf_equivDet_of_cellDecomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:08.687706+00:00
-- url     : https://prove2.me/submissions/e63f9086-bb91-4dd2-ab4c-c34197dad44d

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellInversePair
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_jf_psiOnto_of_cellDecomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_equiv_det_of_onto


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution (hCD : BigCellDecomposition.CellDecomp) : Formalism.FourierDecayAlt.JF.EquivDet :=
  Formalism.FourierDecayAlt.P.equiv_det_of_onto (jf_psiOnto_of_cellDecomp hCD)
end Formalism.FourierDecayAlt.P
