-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.kappa_formula_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:27.602802+00:00
-- url     : https://prove2.me/submissions/b8427c1d-16b8-460b-8625-6563d9ae12fd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_kap_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.KapFormula := by
  intro K S _ _ q w L _ _ h
  exact Formalism.FourierDecayAlt.P.Wd10.kap_eq q w L h
end Formalism.FourierDecayAlt.P
