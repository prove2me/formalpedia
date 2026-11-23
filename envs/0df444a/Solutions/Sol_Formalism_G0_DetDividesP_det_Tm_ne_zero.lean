-- Prove2me | solution 1 for Formalism.G0.DetDividesP.det_Tm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:05.327899+00:00
-- url     : https://prove2.me/submissions/e4698815-8c18-4fa7-bcd8-1fb08fec5598

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_evPerm_Tm
import Theorems.Thm_Formalism_G0_DetDividesP_sign_cast_ne_zero

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
theorem _root_.solution (A : Fin r → ι) (hA : Function.Injective A) : (Tm K A).det ≠ 0 := by
  intro h
  have := congrArg (evPerm (K := K) A 1) h
  rw [AlgHom.map_det, evPerm_Tm A hA, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) 1 this
end Formalism.G0.DetDividesP
