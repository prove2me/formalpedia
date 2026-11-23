-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.Q0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:53.076058+00:00
-- url     : https://prove2.me/submissions/ace2d3ed-5e4e-4167-b7a1-deb3c80e71e4

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_X0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OneLevelCoefficients
open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients
theorem _root_.solution (D : Data E W) (T : Tower E) (ε : ℝ) (w : W) :
    D.Q T ε 0 w = (D.gram ε 0 w [] []).re / D.wt w := by
  simp [Data.Q, Data.Sf, X0, D.K0]
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
