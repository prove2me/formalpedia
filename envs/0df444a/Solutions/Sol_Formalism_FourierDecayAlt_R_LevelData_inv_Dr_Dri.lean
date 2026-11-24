-- Prove2me | solution 1 for Formalism.FourierDecayAlt.R.LevelData.inv_Dr_Dri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.6959+00:00
-- url     : https://prove2.me/submissions/f4e9f94a-8aa4-4d0c-a792-bf4c522d331f

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleInv
import Theorems.Thm_Formalism_FourierDecayAlt_R_PInv_prod_mul_prod_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_fcomm
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_c
import Theorems.Thm_Formalism_FourierDecayAlt_R_LevelData_inv_mem_ci

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
theorem _root_.solution : L.Dr * L.Dri = 1 :=
  prod_mul_prod_eq_one r L.c L.ci L.c_ci (fun i j => L.inv_fcomm (L.inv_mem_c i) (L.inv_mem_ci j))
end _root_.Formalism.FourierDecayAlt.R.LevelData
end Formalism.FourierDecayAlt.R.PInv
