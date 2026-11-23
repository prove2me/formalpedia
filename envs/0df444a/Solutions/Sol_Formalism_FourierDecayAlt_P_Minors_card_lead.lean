-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Minors.card_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:58.829805+00:00
-- url     : https://prove2.me/submissions/9c13aa41-3fe4-4e00-a6be-5b1284eb36ec

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Theorems.Thm_Formalism_FourierDecayAlt_P_Minors_card_lead_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Minors_card_lead_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Minors
open Matrix
variable {K : Type} [Field K]
variable [Fintype K]
namespace Formalism.FourierDecayAlt.P.Minors
theorem _root_.solution (r : ℕ) :
    Nat.card {C : Matrix (Fin r) (Fin r) K // Lead r C} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r := by
  induction r with
  | zero => simpa using card_lead_zero
  | succ r ih =>
    rw [card_lead_succ, ih]
    have h1 : (r + 1) ^ 2 - (r + 1) = r ^ 2 - r + r + r := by
      have : r ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r
      have : (r + 1) ^ 2 = r ^ 2 + 2 * r + 1 := by ring
      omega
    rw [h1, pow_add, pow_add, pow_succ]
    ring
end Formalism.FourierDecayAlt.P.Minors
