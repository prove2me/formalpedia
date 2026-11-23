-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.ins_J
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:47.85836+00:00
-- url     : https://prove2.me/submissions/c827da45-7e34-452e-bc39-332147efc2a2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries

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
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution (a : S) : ins a JJ = eU a 0 1 - eU a 1 0 := by
  simp [ins, Formalism.YangianSpanCharacter.T.J, Fin.sum_univ_two, sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.Wd9
