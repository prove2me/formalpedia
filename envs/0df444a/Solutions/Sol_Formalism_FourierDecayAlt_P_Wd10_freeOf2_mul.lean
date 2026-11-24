-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd10.freeOf2_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:28.263415+00:00
-- url     : https://prove2.me/submissions/315fe37e-5419-45a9-a09f-5d90293cade5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd10_free_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_free_zero


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
theorem _root_.solution {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact Finset.sum_induction _ (FreeOf a) (fun _ _ => free_add) (free_zero a)
    (fun k _ => free_mul (hM i k) (hN k j))
end Formalism.FourierDecayAlt.P.Wd10
