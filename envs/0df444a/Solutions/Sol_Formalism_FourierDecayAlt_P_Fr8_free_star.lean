-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.free_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:19.468448+00:00
-- url     : https://prove2.me/submissions/e8692118-e327-41ae-95b5-4122e5d21795

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution [StarRing A] {c : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf c b) : FreeOf c (star b) := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf at h ⊢
  intro i j
  have key : star (Formalism.FourierDecayAlt.Wd.eU c j i : SlopeTestRemainingChoices S A) = Formalism.FourierDecayAlt.Wd.eU c i j := by
    refine Matrix.ext fun x y => ?_
    simp only [Matrix.star_apply, Formalism.FourierDecayAlt.Wd.eU, Matrix.of_apply]
    by_cases h1 : y c = j ∧ x c = i ∧ ∀ b, b ≠ c → y b = x b
    · rw [if_pos h1, if_pos ⟨h1.2.1, h1.1, fun b hb => (h1.2.2 b hb).symm⟩, star_one]
    · rw [if_neg h1, if_neg (fun h2 => h1 ⟨h2.2.1, h2.1, fun b hb => (h2.2.2 b hb).symm⟩), star_zero]
  have hs := (h j i).star_star
  rwa [key] at hs
end Formalism.FourierDecayAlt.P.Fr8
