-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.di_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:05:37.489808+00:00
-- url     : https://prove2.me/submissions/3c9951b3-6beb-4284-988b-e1b7ea1a34e0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_wti_wt

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
namespace Formalism.FourierDecayAlt.P.Fr3
theorem _root_.solution (hf : IsFrame L f) : f.di L * f.d L = 1 := by
  have p : ∀ n : ℕ, (wti L : SlopeTestRemainingChoices S A) ^ n * wt L ^ n = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, pow_succ', mul_assoc, ← mul_assoc (wti L), wti_wt, one_mul, ih]
  unfold FrameData.di FrameData.d
  rw [mul_assoc, ← mul_assoc (wti L ^ f.N), p, one_mul, hf.c_ci.2]
end Formalism.FourierDecayAlt.P.Fr3
