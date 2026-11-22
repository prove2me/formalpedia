-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.cj_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:58:06.821926+00:00
-- url     : https://prove2.me/submissions/55901f49-76cf-4541-9717-69fabba62df9

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_cj_apply

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
theorem _root_.solution {x : A} (hx : x * g = g * x) : cj g gi h h' x = x := by
  rw [cj_apply, mul_assoc, hx, ← mul_assoc, h', one_mul]
end Formalism.FourierDecayAlt.P.RuleGD
