-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.nabs_zbi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:53.4566+00:00
-- url     : https://prove2.me/submissions/673da60e-c6d5-4852-b82f-9f4474d987e9

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_multiplierPair_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_nabsE_fn
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eci

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (a TT : ℝ) : nabsE a TT * (zbiP : Pr r) = zbiP * nabsE a TT + zbiP * zbiP := by
  rw [zbiP, nabsE_fn, eci, eci, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2 <;> ring
end Formalism.FourierDecayAlt.P.Mx2
