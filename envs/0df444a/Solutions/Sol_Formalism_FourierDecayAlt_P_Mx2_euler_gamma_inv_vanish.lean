-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.euler_gamma_inv_vanish
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:58.200359+00:00
-- url     : https://prove2.me/submissions/45257dfd-5daf-4dd7-a91e-878b1a82865a

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_gg_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx2_euler_gamma_vanish

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
theorem _root_.solution (v : Var r) (h1 : v ≠ vz) (h2 : v ≠ vzb) (TT : ℝ) : euler v (gg TT : Fn r)⁻¹ = 0 := by
  rw [euler_inv _ _ (gg_ne TT), euler_gamma_vanish v h1 h2]; simp
end Formalism.FourierDecayAlt.P.Mx2
