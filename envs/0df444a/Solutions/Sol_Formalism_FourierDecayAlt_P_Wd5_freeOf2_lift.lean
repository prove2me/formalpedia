-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.freeOf2_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:27.396262+00:00
-- url     : https://prove2.me/submissions/d8c424c0-ff76-427d-9c1f-1e813ed9f32b

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_io

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd5
open Matrix Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd5
theorem _root_.solution (c : S) (M : M2 A) : FreeOf2 c (lift0 M : M2 (SlopeTestRemainingChoices S A)) := fun i j => free_io c (M i j)
end Formalism.FourierDecayAlt.P.Wd5
