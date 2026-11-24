-- Prove2me | solution 1 for Formalism.Q3.exists_square_roots_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:21.100615+00:00
-- url     : https://prove2.me/submissions/72ca47ed-5899-4f95-9efe-a47930b36fdf

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {k : ℕ} (a : Fin k → ℤ)
namespace Formalism.Q3
theorem _root_.solution : ∃ β : Fin k → AlgebraicClosure ℚ, ∀ i, β i ^ 2 = (a i : AlgebraicClosure ℚ) := by
  choose β hβ using fun i => IsAlgClosed.exists_pow_nat_eq ((a i : AlgebraicClosure ℚ)) two_pos
  exact ⟨β, hβ⟩
end Formalism.Q3
