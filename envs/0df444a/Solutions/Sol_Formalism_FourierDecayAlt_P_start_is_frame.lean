-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.start_is_frame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:49:54.318688+00:00
-- url     : https://prove2.me/submissions/987b30e4-26e8-4181-907a-ef9ae51ae325

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : StartFrame := by
  intro hSM A S _ _ _ _ _ _ r L st hst
  have hio_mul : ∀ a b : A, (io (a * b) : SlopeTestRemainingChoices S A) = io a * io b := fun a b => by
    simp only [io, map_mul]
  have hio_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by simp only [io, map_one]
  have hio_comm : ∀ a b : A, Commute a b → Commute (io a : SlopeTestRemainingChoices S A) (io b) := fun a b h => by
    simp only [io]
    exact h.map _
  have hio_star : ∀ a : A, star (io a : SlopeTestRemainingChoices S A) = io (star a) := fun a => by
    ext i j
    by_cases h : i = j
    · subst h
      simp [io, Matrix.star_apply, Matrix.scalar_apply]
    · simp [io, Matrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply, h, Ne.symm h]
  refine
    { module := ?_, lowerLeftEntry_commute := ?_, inv_reg := ?_, F_Fi := ?_, Fi_F := ?_, x_xi := ?_, c_ci := ?_,
      x_commute := ?_, x_c := ?_, x_fn := ?_, x_nab := ?_, c_fn := ?_, x_star := ?_, c_star := ?_,
      ee_fn := ?_, form := ?_, frame_τ := ?_, frame_l := ?_ }
  all_goals dsimp only [Start.frame]
  · exact hSM ℂ A S st.QQ st.q hst.start
  · intro Y _ Y' _
    simp only [lift0, Matrix.map_apply]
    exact hio_comm _ _ (hst.lowerLeftEntry_commute Y Y')
  · exact Set.subset_univ _
  · exact mul_one 1
  · exact mul_one 1
  · intro Y hY
    exact ⟨by rw [← hio_mul, (hst.x_xi Y hY).1, hio_one], by rw [← hio_mul, (hst.x_xi Y hY).2, hio_one]⟩
  · exact ⟨mul_one 1, mul_one 1⟩
  · intro Y Y'
    exact hio_comm _ _ (hst.x_commute Y Y')
  · intro Y
    exact Commute.one_right _
  · intro Y g hg
    exact hio_comm _ _ (hst.x_fn Y g hg)
  · intro Y
    exact hio_comm _ _ (hst.x_nab Y)
  · intro g _
    exact Commute.one_left _
  · intro Y hY
    rw [hio_star, hst.x_star Y hY]
  · exact star_one _
  · intro Y g hg
    exact hio_comm _ _ (hst.ee_fn Y g hg)
  · simp [Formalism.FourierDecayAlt.Fr.FrameData.d, Start.frame]
  · intro Y _
    simp only [lift0, Matrix.map_apply, one_mul, mul_one]
    rw [hst.tau Y]
    simp only [io, map_mul]
  · intro Y hY _
    simp only [lift0, Matrix.map_apply, one_mul, mul_one, Formalism.FourierDecayAlt.Fr.FrameData.l, Formalism.FourierDecayAlt.Fr.kapL]
    rw [hst.low Y hY]
    simp only [io, map_mul, map_add]
end Formalism.FourierDecayAlt.P
