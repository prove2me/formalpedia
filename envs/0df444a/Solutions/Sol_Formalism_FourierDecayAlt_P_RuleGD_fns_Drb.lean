-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.fns_Drb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:20.379486+00:00
-- url     : https://prove2.me/submissions/d2ae2492-6ea6-4574-bbab-ae7340feb6bd

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fc
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_comm_Drb

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
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (L : LevelData A r) {x : A} (hx : x ∈ L.fns) : x * L.Drb = L.Drb * x :=
  comm_Drb L (fun l => fc L hx (m_cb L l))
end Formalism.FourierDecayAlt.P.RuleGD
