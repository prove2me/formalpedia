-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.free_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:18.567985+00:00
-- url     : https://prove2.me/submissions/2d9831b8-23c0-45f0-b568-384ec68c61c1

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution {a : S} {M : SlopeTestRemainingChoices S A} (hM : FreeOf a M) {z y : Ix S} (h : z a ≠ y a) :
    M z y = 0 := by
  have h1 := congrFun (congrFun (hM (z a) (z a)).eq z) y
  rw [eU_mul_apply, mul_eU_apply, if_pos rfl, if_neg (Ne.symm h), Function.update_eq_self] at h1
  exact h1
end Formalism.FourierDecayAlt.P.Wd7
