-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.mem_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:35:58.631485+00:00
-- url     : https://prove2.me/submissions/363ea5d8-4f01-47cc-bd1a-a2c0cd8f8d92

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (L : LevelData A r) (st : Start A) (w : List (Letter ℂ S)) (Y : ℂ)
    (h0 : Y ∈ st.inv) (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ 1 ∧ Y - l.pt ≠ -1) :
    Y ∈ (ofWord L st w).inv := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [ofWord, hp, if_true, FrameData.plus]
      exact ⟨ih', hl.1, hl.2.1⟩
    · simp only [ofWord, hp, FrameData.minus]
      refine ⟨ih', ?_, ?_⟩
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2.2; linear_combination -e
end Formalism.FourierDecayAlt.P.Fr2
