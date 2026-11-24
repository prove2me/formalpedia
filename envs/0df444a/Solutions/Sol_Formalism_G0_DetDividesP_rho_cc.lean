-- Prove2me | solution 1 for Formalism.G0.DetDividesP.rho_cc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:39.340964+00:00
-- url     : https://prove2.me/submissions/d0c4addc-bff3-4cf0-abcd-d8a4701c8857

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_rho_adj

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
theorem _root_.solution (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    rho K A l (((Tm K A).adjugate.mulVec (Wv K A)) lst) = (Tm K A).adjugate lst l := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, rho_adj]
  have : ∀ j, rho K A l (Wv K A j) = if j = l then 1 else 0 := by
    intro j; simp [rho, Wv, hA.eq_iff]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end Formalism.G0.DetDividesP
