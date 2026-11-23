-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.freeOf2_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:59.074582+00:00
-- url     : https://prove2.me/submissions/64a110c7-af0c-4d37-a885-2fe18f52c4d3

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_zero

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
theorem _root_.solution (c : S) : FreeOf2 c (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact free_one c
  · exact free_zero c
end Formalism.FourierDecayAlt.P.Wd5
