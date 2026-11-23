-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.leftCorrection_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:20.168901+00:00
-- url     : https://prove2.me/submissions/8c2eb34b-41ac-4e9e-8b7b-ee7700271e28

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
theorem _root_.solution {h : A} (hn : Commute L.nab h) (hz : Commute L.ζb h) (hg : Commute L.GGi h) (Y : ℂ) :
    L.l0 Y * h = h * L.l0 Y := by
  unfold LevelData.l0
  exact ((hn.neg_left).sub_left ((Algebra.commute_algebraMap_left _ h).mul_left (hz.mul_left hg))).eq
end Formalism.FourierDecayAlt.P.RuleSS
