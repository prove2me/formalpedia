-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.PInv.comm_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.730697+00:00
-- url     : https://prove2.me/submissions/cb506a53-d798-4b80-99b6-7395ed46e539

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.PInv
open Matrix LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.R.PInv
theorem _root_.solution (x : A) (y : ℂ) : Commute x (algebraMap ℂ A y) := Algebra.commute_algebraMap_right y x
end Formalism.FourierDecayAlt.R.PInv
