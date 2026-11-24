-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.zc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:25:20.376007+00:00
-- url     : https://prove2.me/submissions/241b8170-ed2f-4ac0-913d-c6837eda7ff2

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_zsub

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
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : Commute x y :=
  L.fns_comm x (zsub L hx) y (zsub L hy)
end Formalism.FourierDecayAlt.P.Fr3
