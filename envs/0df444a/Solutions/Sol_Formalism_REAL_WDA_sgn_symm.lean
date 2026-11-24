-- Prove2me | solution 1 for Formalism.REAL.WDA_sgn_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:13.039932+00:00
-- url     : https://prove2.me/submissions/9fd7e19b-7145-4a81-bbf9-21dabafee4c1

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
theorem _root_.solution (ε : Fin n → Bool) (a b : Fin n) : sgn ε a b = sgn ε b a := by
  unfold sgn; simp only [eq_comm]
end Formalism.REAL
