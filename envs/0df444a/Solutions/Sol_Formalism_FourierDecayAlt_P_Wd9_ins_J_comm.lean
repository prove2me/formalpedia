-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.ins_J_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:12.663658+00:00
-- url     : https://prove2.me/submissions/0bf19832-bd2a-4c4d-993b-96ad95077e07

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_comm_J
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) : b * ins a JJ = ins a JJ * b :=
  (Wd1.ins_comm a JJ b hb (comm_J b)).eq
end Formalism.FourierDecayAlt.P.Wd9
