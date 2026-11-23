-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:14.793791+00:00
-- url     : https://prove2.me/submissions/cce2e2d7-24ec-424e-a22d-d848d11c2989

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_estBlockOfSumForm_ok

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
end Formalism.FourierDecayAlt.P
