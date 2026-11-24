-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:04.2828+00:00
-- url     : https://prove2.me/submissions/86ef75dd-e5b6-48da-a892-f9f2b84f3654

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_add
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_monomial

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
theorem _root_.solution {σ : Type} (c : K) (P Q : MvPolynomial σ K) :
    diffOp (MvPolynomial.C c * P) Q = c • diffOp P Q := by
  rw [C_mul']
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [smul_monomial, smul_eq_mul, diffOp_monomial, diffOp_monomial, mul_smul]
  | add p q hp hq => rw [smul_add, diffOp_add, diffOp_add, hp, hq, smul_add]
end Formalism.IncomingBounds.Cay
