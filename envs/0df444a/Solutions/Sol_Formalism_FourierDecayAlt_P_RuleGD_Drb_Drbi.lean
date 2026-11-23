-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.Drb_Drbi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:20.299572+00:00
-- url     : https://prove2.me/submissions/168b2715-ce18-4ca7-acbd-ebc5a77817cd

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
theorem _root_.solution (L : LevelData A r) : L.Drb * L.Drbi = 1 :=
  prod_mul_prod_eq_one L.cb L.cbi L.cb_cbi (fun i j => fc L (m_cbi L i) (m_cb L j))
end Formalism.FourierDecayAlt.P.RuleGD
