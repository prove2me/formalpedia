-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.m_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:39.275691+00:00
-- url     : https://prove2.me/submissions/cdf9ead3-fd1e-48ee-aa4b-0446f697f38e

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
variable (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (l) : L.c l ∈ L.fns := by simp [LevelData.fns]
end Formalism.FourierDecayAlt.P.RuleGD
