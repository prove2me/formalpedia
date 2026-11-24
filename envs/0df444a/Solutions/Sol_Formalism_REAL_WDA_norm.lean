-- Prove2me | solution 1 for Formalism.REAL.WDA_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:09.183358+00:00
-- url     : https://prove2.me/submissions/6f6fbb9d-8d77-4c46-8fc9-f218228f250c

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (hU : IsUnitary ε E) (a b : Fin n) (x : V) :
    (((‖E a b x‖ ^ 2 : ℝ)) : ℂ) = (sgn ε a b : ℂ) * ⟪x, E b a (E a b x)⟫_ℂ := by
  rw [Complex.ofReal_pow, ← hU a b x (E a b x)]
  exact (inner_self_eq_norm_sq_to_K (E a b x)).symm
end Formalism.REAL
