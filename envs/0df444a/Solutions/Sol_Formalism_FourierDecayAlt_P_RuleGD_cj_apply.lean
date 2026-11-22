-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.cj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:54:41.612188+00:00
-- url     : https://prove2.me/submissions/3a83214c-96e6-4cd5-a56c-a4f1a723107b

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
variable (g gi : A) (h : g * gi = 1) (h' : gi * g = 1)
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (x : A) : cj g gi h h' x = gi * x * g := rfl
end Formalism.FourierDecayAlt.P.RuleGD
