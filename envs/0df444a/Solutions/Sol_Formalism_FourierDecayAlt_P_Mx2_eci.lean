-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.eci
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:58.181135+00:00
-- url     : https://prove2.me/submissions/7a77d256-128f-44fc-9326-fc447d8bfd8b

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_ec

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
theorem _root_.solution (v w : Var r) : euler v (coord w)⁻¹ = if v = w then -(coord w)⁻¹ else 0 := by
  rw [euler_inv _ _ (coord_ne r w), ec]
  split_ifs
  · field_simp [coord_ne r w]
  · simp
end Formalism.FourierDecayAlt.P.Mx2
