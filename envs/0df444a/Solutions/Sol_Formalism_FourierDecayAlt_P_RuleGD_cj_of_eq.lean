-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.cj_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:15.386526+00:00
-- url     : https://prove2.me/submissions/e19fbf2b-609c-44a8-a0ff-48af9f2f653f

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
theorem _root_.solution {x a : A} (hx : x * g = g * x + a * g) : cj g gi h h' x = x + cj g gi h h' a := by
  rw [cj_apply, cj_apply, mul_assoc, hx, mul_add, ← mul_assoc, h', one_mul, ← mul_assoc]
end Formalism.FourierDecayAlt.P.RuleGD
