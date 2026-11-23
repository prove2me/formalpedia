-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.budget_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:08.021238+00:00
-- url     : https://prove2.me/submissions/703fac58-184f-44f2-95f0-1a30a0baa182

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_OneLevelCoefficients_budget_step

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
theorem _root_.solution (K r i s c m : ℕ) (hsi : s ≤ i) (hi : i ≤ r + 1)
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1) :=
  (budget_step K r i s c m hsi hi hc hm).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
