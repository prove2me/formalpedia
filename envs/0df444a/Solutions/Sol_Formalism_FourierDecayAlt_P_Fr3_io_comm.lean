-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.io_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:21:01.398598+00:00
-- url     : https://prove2.me/submissions/55bebfdc-16ea-47fa-a3b1-e08fa61804ac

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_io_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr3
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  unfold Commute SemiconjBy
  rw [← io_mul, ← io_mul, h.eq]
end Formalism.FourierDecayAlt.P.Fr3
