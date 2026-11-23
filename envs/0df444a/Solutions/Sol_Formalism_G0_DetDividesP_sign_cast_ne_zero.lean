-- Prove2me | solution 1 for Formalism.G0.DetDividesP.sign_cast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:41:45.357814+00:00
-- url     : https://prove2.me/submissions/f9e224af-1a2e-43e8-bc05-0afbe9164a83

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution (τ : Equiv.Perm (Fin r)) : ((Equiv.Perm.sign τ : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
end Formalism.G0.DetDividesP
