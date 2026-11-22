-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.cj_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:14.232728+00:00
-- url     : https://prove2.me/submissions/02700e57-994d-4839-9201-7c73308b401c

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_fix

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
theorem _root_.solution (z : ℂ) : cj g gi h h' (algebraMap ℂ A z) = algebraMap ℂ A z :=
  cj_fix g gi h h' (Algebra.commutes z g)
end Formalism.FourierDecayAlt.P.RuleGD
