-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr3.hat_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:02.466796+00:00
-- url     : https://prove2.me/submissions/b39b05e4-a8db-44e5-a2e1-d592d37289a3

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L0ConstantPartCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_hat_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr3_cancel2

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
theorem _root_.solution (hf : IsFrame L f) {Z : ℂ} (hZ : Z ∈ f.reg) (hr : star Z = Z) (i j : Fin 2) :
    star (f.d L * f.hatT Z i j) = f.d L * f.hatT Z j i := by
  have h0 := hf.module.herm Z hZ hr
  have hh : ∀ i j, star (f.RR * f.TT Z i j) = f.RR * f.TT Z j i := by
    intro i j
    have := congrFun (congrFun h0 j) i
    simpa [d0, Matrix.conjTranspose_apply, Matrix.diagonal_mul] using this
  have hF : ∀ i j, f.RR * f.TT Z i j = star f.F * (f.d L * f.hatT Z i j) * f.F := by
    intro i j
    rw [hat_apply hZ, hf.form]
    calc star f.F * f.d L * f.F * f.TT Z i j
        = star f.F * f.d L * f.F * f.TT Z i j * (f.Fi * f.F) := by rw [hf.Fi_F, mul_one]
      _ = _ := by simp only [mul_assoc]
  have sF : star f.Fi * star f.F = 1 := by rw [← star_mul, hf.F_Fi, star_one]
  refine cancel2 sF hf.F_Fi ?_
  have := hh i j
  rw [hF i j, hF j i, star_mul, star_mul, star_star, ← mul_assoc] at this
  exact this
end Formalism.FourierDecayAlt.P.Fr3
