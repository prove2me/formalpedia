-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.mul_eU_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:54:27.831864+00:00
-- url     : https://prove2.me/submissions/4346e58c-26ec-4355-82a3-fcccd2e4db23

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Wd7_eU_apply__f51f2867f050

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
theorem _root_.solution (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    (B * (eU a i j : SlopeTestRemainingChoices S A)) x y = if y a = j then B x (Function.update y a i) else 0 := by
  rw [Matrix.mul_apply]
  simp only [eU_apply']
  by_cases h : y a = j
  · simp [h]
  · simp [h]
end Formalism.FourierDecayAlt.P.Wd7
