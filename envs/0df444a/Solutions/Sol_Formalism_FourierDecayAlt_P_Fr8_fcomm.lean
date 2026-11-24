-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.fcomm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:07:03.15164+00:00
-- url     : https://prove2.me/submissions/0b0528c7-7f17-4bcc-93b9-704e381e0001

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
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution (L : LevelData A r) {x y : A} (hx : x ∈ zfns L) (hy : y ∈ zfns L) : Commute x y := by
  obtain ⟨p, pb, c, ci, cb, cbi, ζ, ζi, ζb, ζbi, GG, GGi, nab, nabs, TT, hc⟩ := L
  exact hc x (Set.mem_union_right _ hx) y (Set.mem_union_right _ hy)
end Formalism.FourierDecayAlt.P.Fr8
