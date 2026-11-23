-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.add_comm0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:28.365858+00:00
-- url     : https://prove2.me/submissions/d8169c47-deca-450f-94c3-b11b75236899

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
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution {x h : A} (hx : Commute x h) (Y : ℂ) :
    (algebraMap ℂ A Y + x) * h = h * (algebraMap ℂ A Y + x) :=
  ((Algebra.commute_algebraMap_left Y h).add_left hx).eq
end Formalism.FourierDecayAlt.P.RuleSS
