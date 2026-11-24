-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd5.free_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:02.6869+00:00
-- url     : https://prove2.me/submissions/7ca2deff-5694-4782-a4ba-0d8820d98b1c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferMatrixFactorization
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd5_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_comm_of_ne


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
theorem _root_.solution {a c : S} (hc : c ≠ a) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro p q
  unfold ins
  exact Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
    (eU_comm_of_ne hc p q i j).mul_right (hM i j p q)
end Formalism.FourierDecayAlt.P.Wd5
