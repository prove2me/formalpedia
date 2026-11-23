-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.Kw_nil
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:57:50.446944+00:00
-- url     : https://prove2.me/submissions/3636d6bd-5389-4026-a2c0-3b5c14098827

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
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution {r : ℕ} (L : LevelData A r) : (Kw L ([] : List (Letter ℂ S)) : SlopeTestRemainingChoices S A) = 0 := by
  simp [Kw]
end Formalism.FourierDecayAlt.P.Fr11
