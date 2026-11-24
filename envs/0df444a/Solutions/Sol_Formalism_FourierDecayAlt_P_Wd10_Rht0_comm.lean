-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.Rht0_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:00.533424+00:00
-- url     : https://prove2.me/submissions/8b599b72-675d-4e40-9373-976058763bbb

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_partial_flip_commute_diagScalar_of_free

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
theorem _root_.solution {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (d : K) :
    Rht0 a d * d0 x = d0 x * Rht0 a d := by
  simp only [Rht0, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, partial_flip_commute_diagScalar_of_free hx]
end Formalism.FourierDecayAlt.P.Wd10
