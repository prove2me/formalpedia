-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.dualCorrection_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:28.479839+00:00
-- url     : https://prove2.me/submissions/f69ee7a5-7b20-460d-af11-4300cb30742e

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {h : A} (hn : Commute L.nabs h) (hz : Commute L.ζ h) (hg : Commute L.GGi h) (Y : ℂ) :
    L.m0 Y * h = h * L.m0 Y := by
  unfold LevelData.m0
  exact ((hn.neg_left).sub_left ((Algebra.commute_algebraMap_left _ h).mul_left (hz.mul_left hg))).eq
end Formalism.FourierDecayAlt.P.RuleSS
