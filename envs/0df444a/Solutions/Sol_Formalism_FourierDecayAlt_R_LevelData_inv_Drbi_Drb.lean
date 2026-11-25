-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_Drbi_Drb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:49:27.104439+00:00
-- url     : https://prove2.me/submissions/035b7efe-739b-4dfe-bf3b-ffdb8f333259

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_prod_mul_prod_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cb
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_cbi

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
namespace _root_.Formalism.FourierDecayAlt.R.LevelData
theorem _root_.solution : L.Drbi * L.Drb = 1 :=
  prod_mul_prod_eq_one r L.cbi L.cb L.cbi_cb (fun i j => L.inv_fcomm (L.inv_mem_cbi i) (L.inv_mem_cb j))
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
