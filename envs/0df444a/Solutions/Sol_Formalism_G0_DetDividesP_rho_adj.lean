-- Prove2me | solution 1 for Formalism.G0.DetDividesP.rho_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:04.795911+00:00
-- url     : https://prove2.me/submissions/be7a8b8b-0786-4be5-8f35-18aed79f647f

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_rho_Tm

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
theorem _root_.solution (A : Fin r → ι) (l i j : Fin r) : rho K A l ((Tm K A).adjugate i j) = (Tm K A).adjugate i j := by
  have := RingHom.map_adjugate (rho K A l).toRingHom (Tm K A)
  have h2 : (rho K A l).toRingHom.mapMatrix (Tm K A) = Tm K A := rho_Tm A l
  rw [h2] at this
  exact congrFun (congrFun this i) j
end Formalism.G0.DetDividesP
