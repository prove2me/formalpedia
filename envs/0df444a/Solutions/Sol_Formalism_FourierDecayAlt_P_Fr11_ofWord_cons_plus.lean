-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.ofWord_cons_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:53.983619+00:00
-- url     : https://prove2.me/submissions/feef5f91-1616-439c-8a61-8ed1ad5e5e33

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
variable {r : ℕ} (L : LevelData A r) (st : Start A)
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (l : Letter ℂ S) (w : List (Letter ℂ S)) (h : l.plus = true) :
    ofWord L st (l :: w) = (ofWord L st w).plus L l.intersection_update_fsHerm_neg_one l.pt := by
  simp [ofWord, h]
end Formalism.FourierDecayAlt.P.Fr11
