-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.twine_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:59.495876+00:00
-- url     : https://prove2.me/submissions/bbdd1cfb-f7b8-4d14-bc43-4ea00d0ed6ca

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_mul_diagScalar_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd10
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd10
theorem _root_.solution {M M' : M2 (SlopeTestRemainingChoices S A)} {x : SlopeTestRemainingChoices S A} {c : K}
    (h : M * d0 x = c • (d0 x * M')) (i j : Fin 2) : M i j * x = c • (x * M' i j) := by
  have e := congrFun (congrFun h i) j
  rwa [mul_diagScalar_apply, Matrix.smul_apply, diagScalar_mul_apply] at e
end Formalism.FourierDecayAlt.P.Wd10
