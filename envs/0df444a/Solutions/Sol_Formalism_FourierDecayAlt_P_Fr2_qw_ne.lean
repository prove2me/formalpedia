-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.qw_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:03.164645+00:00
-- url     : https://prove2.me/submissions/09bdc060-e854-4fb2-895f-d9783036b35e

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
theorem _root_.solution (q : ℂ → ℂ) (w : List (Letter ℂ S)) (Y : ℂ) (h0 : q Y ≠ 0)
    (h : ∀ l ∈ w, Y - l.pt ≠ 0 ∧ Y - l.pt ≠ -1) : qw q w Y ≠ 0 := by
  induction w with
  | nil => exact h0
  | cons l w ih =>
    have hl := h l (by simp)
    have ih' := ih (fun l' hl' => h l' (by simp [hl']))
    by_cases hp : l.plus
    · simp only [qw, hp, if_true]
      refine mul_ne_zero ih' (div_ne_zero ?_ hl.1)
      intro e; apply hl.2; linear_combination e
    · simp only [qw, hp]
      refine mul_ne_zero ih' (div_ne_zero ?_ ?_)
      · intro e; apply hl.1; linear_combination -e
      · intro e; apply hl.2; linear_combination -e
end Formalism.FourierDecayAlt.P.Fr2
