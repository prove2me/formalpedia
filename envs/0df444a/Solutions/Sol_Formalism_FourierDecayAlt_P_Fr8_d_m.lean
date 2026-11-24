-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.d_m
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:41:03.050309+00:00
-- url     : https://prove2.me/submissions/858bebf5-b91d-4b6c-9431-dbee01f0b51a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr8_star_d
import Theorems.Thm_Formalism_FourierDecayAlt_P_adjoint_l_shift_relation
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (hS : IsStarLevel L) (h : IsFrame L f) (Yb : ℂ) (hr : star Yb = Yb) (h0 : Yb ∈ f.inv)
    (h1 : Yb - 1 ∈ f.inv) :
    f.d L * mf f.hatT (fun Y => io L.GGi * f.xi Y) Yb = star (f.l L (Yb - 1)) * f.d L := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have h1' : Yb - 1 + 1 ∈ f.inv := by rwa [sub_add_cancel]
  have hr1 : star (Yb - 1) = Yb - 1 := by rw [star_sub, hr, star_one]
  have hreg := h.inv_reg h1
  have hT : ∀ i j, f.hatT (Yb - 1) i j = f.F * f.TT (Yb - 1) i j * f.Fi := by
    intro i j; simp [FrameData.hatT, hreg]
  have sF : star f.Fi * star f.F = 1 := by rw [← star_mul, h.F_Fi, star_one]
  have key : ∀ i j, f.d L * f.hatT (Yb - 1) i j = star f.Fi * (f.RR * f.TT (Yb - 1) i j) * f.Fi := by
    intro i j
    rw [hT, h.form]
    calc f.d L * (f.F * f.TT (Yb - 1) i j * f.Fi)
        = (star f.Fi * star f.F) * f.d L * f.F * f.TT (Yb - 1) i j * f.Fi := by
          rw [sF, one_mul]; simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  have herm := h.module.herm _ hreg hr1
  have he : ∀ i j, star (f.RR * f.TT (Yb - 1) i j) = f.RR * f.TT (Yb - 1) j i := by
    intro i j
    have := congrFun (congrFun herm j) i
    simpa [Matrix.conjTranspose_apply, d0, Matrix.diagonal_mul] using this
  have hh : ∀ i j, star (f.d L * f.hatT (Yb - 1) i j) = f.d L * f.hatT (Yb - 1) j i := by
    intro i j
    rw [key, key, star_mul, star_mul, star_star, he]
    simp only [mul_assoc]
  have e := adjoint_l_shift_relation ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv (f.d L) H (star_d hS h) (Yb - 1) h1 h1' hh
  rw [sub_add_cancel, Hl (Yb - 1) h1 h1'] at e
  exact e
end Formalism.FourierDecayAlt.P.Fr8
