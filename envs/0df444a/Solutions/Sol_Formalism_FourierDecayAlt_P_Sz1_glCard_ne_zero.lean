-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.glCard_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:21.88984+00:00
-- url     : https://prove2.me/submissions/55df21c9-ed2e-4f71-a470-6ddf0d37e6c0

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_glCard_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz1_prod_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution (k : ℕ) (q : ℝ) (hq : 1 < q) : glCard k q ≠ 0 := by
  have hq0 : q ≠ 0 := by linarith
  rw [glCard_eq k q hq0]
  exact mul_ne_zero (pow_ne_zero _ hq0) (prod_ne_zero k q hq)
end Formalism.FourierDecayAlt.P.Sz1
