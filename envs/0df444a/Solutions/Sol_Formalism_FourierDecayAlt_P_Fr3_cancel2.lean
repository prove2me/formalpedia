-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.cancel2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:05:00.00447+00:00
-- url     : https://prove2.me/submissions/f5a3f551-2f56-4a0f-a391-08d8e3338cc2

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ} {L : LevelData A r} {f : FrameData S A}
omit [StarRing A] [StarModule ℂ A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution {B : Type} [Ring B] {P Pi Q Qi X Y : B} (h1 : Pi * P = 1) (h2 : Q * Qi = 1)
    (h : P * X * Q = P * Y * Q) : X = Y := by
  calc X = Pi * P * X * (Q * Qi) := by rw [h1, h2, one_mul, mul_one]
    _ = Pi * (P * X * Q) * Qi := by noncomm_ring
    _ = Pi * (P * Y * Q) * Qi := by rw [h]
    _ = Pi * P * Y * (Q * Qi) := by noncomm_ring
    _ = Y := by rw [h1, h2, one_mul, mul_one]
end Formalism.FourierDecayAlt.P.Fr3
