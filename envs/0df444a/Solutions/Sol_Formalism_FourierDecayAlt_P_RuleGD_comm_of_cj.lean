-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.comm_of_cj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:46.165806+00:00
-- url     : https://prove2.me/submissions/de0fdbfc-7df7-42cb-b21f-94ec99ae2e78

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
theorem _root_.solution {y : A} (hy : cj g gi h h' y = y) : g * y = y * g := by
  have := congrArg (g * ·) hy
  simp only [cj_apply, ← mul_assoc, h, one_mul] at this
  exact this.symm
end Formalism.FourierDecayAlt.P.RuleGD
