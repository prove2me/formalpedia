-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.Drbi_Drb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:49.73614+00:00
-- url     : https://prove2.me/submissions/3205425b-9477-4a87-8b9a-809b286cf2c2

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_prod_mul_prod_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_fc
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cb
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_m_cbi

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
theorem _root_.solution (L : LevelData A r) : L.Drbi * L.Drb = 1 :=
  prod_mul_prod_eq_one L.cbi L.cb L.cbi_cb (fun i j => fc L (m_cb L i) (m_cbi L j))
end Formalism.FourierDecayAlt.P.RuleGD
