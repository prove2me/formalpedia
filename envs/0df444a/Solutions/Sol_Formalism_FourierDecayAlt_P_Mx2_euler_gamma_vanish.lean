-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.euler_gamma_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:56.922225+00:00
-- url     : https://prove2.me/submissions/c095122f-1231-4685-81c5-f8746800722f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerLeibniz
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_eulerCoord
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
theorem _root_.solution (v : Var r) (h1 : v ≠ vz) (h2 : v ≠ vzb) (TT : ℝ) : euler v (gg TT : Fn r) = 0 := by
  unfold gg
  rw [map_sub, eulerLeibniz, ec, ec, (eulerCoord r v v _).2, if_neg h1, if_neg h2]; simp
end Formalism.FourierDecayAlt.P.Mx2
