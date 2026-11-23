-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OneLevelCoefficients.budget_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:17.462817+00:00
-- url     : https://prove2.me/submissions/344d7127-56f2-4aa0-826b-2ca001fc31a3

import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelCoefficients

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
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1 - (i - s)) := by
  have h1 : r + 1 - (i - s) = (r + 1 - i) + s := by omega
  have h2 : m * K ≤ 4 * K * s := by
    calc m * K ≤ 4 * s * K := Nat.mul_le_mul_right _ hm
      _ = 4 * K * s := by ring
  rw [h1, Nat.mul_add]
  exact Nat.add_le_add hc h2
end Formalism.FourierDecayAlt.P.OneLevelCoefficients
