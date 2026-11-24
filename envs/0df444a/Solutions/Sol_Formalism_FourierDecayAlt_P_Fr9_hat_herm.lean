-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.hat_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:40:19.073293+00:00
-- url     : https://prove2.me/submissions/a10e4fba-d7df-4280-a95a-c70c60cd6a8d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_hat_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (h : IsFrame L f) {Y : ℂ} (hY : Y ∈ f.reg) (hr : star Y = Y) (i j : Fin 2) :
    star (f.d L * f.hatT Y i j) = f.d L * f.hatT Y j i := by
  have e := congrFun (congrFun (h.module.herm Y hY hr) j) i
  rw [Matrix.conjTranspose_apply, Wd11.diagScalar_mul_apply, Wd11.diagScalar_mul_apply, h.form] at e
  have e1 : ∀ i j, star f.F * f.d L * f.F * f.TT Y i j = star f.F * (f.d L * f.hatT Y i j) * f.F := by
    intro i j
    rw [mul_assoc (star f.F * f.d L), ← hat_F h hY]; simp only [mul_assoc]
  rw [e1, e1, star_mul, star_mul, star_star, ← mul_assoc] at e
  have s : star f.Fi * star f.F = 1 := by rw [← star_mul, h.F_Fi, star_one]
  have cancel : ∀ z, star f.Fi * (star f.F * z * f.F) * f.Fi = z := by
    intro z
    calc star f.Fi * (star f.F * z * f.F) * f.Fi = (star f.Fi * star f.F) * z * (f.F * f.Fi) := by
          simp only [mul_assoc]
      _ = z := by rw [s, h.F_Fi, one_mul, mul_one]
  rw [← cancel (star (f.d L * f.hatT Y i j)), e, cancel]
end Formalism.FourierDecayAlt.P.Fr9
