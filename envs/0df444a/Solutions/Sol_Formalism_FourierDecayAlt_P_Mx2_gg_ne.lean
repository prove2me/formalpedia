-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.gg_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:33.232859+00:00
-- url     : https://prove2.me/submissions/6bbeca7a-9e9b-4a56-a1aa-567f721d6e08

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_coord_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_GG_z

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
theorem _root_.solution (TT : ℝ) : (gg TT : Fn r) ≠ 0 := by
  intro h
  have h1 := euler_GG_z (r := r) TT
  rw [h, map_zero] at h1
  exact mul_ne_zero (coord_ne r vz) (coord_ne r vzb) h1.symm
end Formalism.FourierDecayAlt.P.Mx2
