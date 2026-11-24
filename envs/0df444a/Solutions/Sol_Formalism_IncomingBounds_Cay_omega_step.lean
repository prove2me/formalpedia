-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.omega_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:14.9148+00:00
-- url     : https://prove2.me/submissions/1c1892a3-e41a-491e-a02a-a0fc9aca7df4

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_X_mul
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_C_mul
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_sum

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
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {n k : ℕ} (r c : Fin (k+2) → Fin n) (Q : MvPolynomial (PVar n) K) :
    diffOp ((Mg K n).submatrix r c).det Q =
      ∑ j : Fin (k+2), ((-1 : K) ^ (j : ℕ)) •
        pderiv (Sum.inl (r 0, c j)) (diffOp ((Mg K n).submatrix (r ∘ Fin.succ) (c ∘ j.succAbove)).det Q) := by
  rw [det_succ_row_zero, diffOp_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e2 : ((-1 : MvPolynomial (Formalism.IncomingBounds.PVar n) K) ^ (j : ℕ)) = MvPolynomial.C ((-1 : K) ^ (j : ℕ)) := by
    simp
  rw [Matrix.submatrix_submatrix, e2, Matrix.submatrix_apply, mul_assoc, diffOp_C_mul,
    show Mg K n (r 0) (c j) = X (Sum.inl (r 0, c j)) from rfl, diffOp_X_mul]
end Formalism.IncomingBounds.Cay
