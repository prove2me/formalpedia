-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.diffOp_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:47:43.910623+00:00
-- url     : https://prove2.me/submissions/8019e245-7ffa-4443-b4b8-d46d6a11aaaf

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_add
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_monomial
import Theorems.Thm_Formalism_IncomingBounds_Cay_dm_succ

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
theorem _root_.solution {σ : Type} (x : σ) (P Q : MvPolynomial σ K) :
    diffOp (X x * P) Q = pderiv x (diffOp P Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hX : (X x : MvPolynomial σ K) * monomial u a = monomial (Finsupp.single x 1 + u) a := by
      rw [X, monomial_mul, one_mul]
    rw [hX, diffOp_monomial, diffOp_monomial, dm_succ, Derivation.map_smul]
  | add p q hp hq => rw [mul_add, diffOp_add, diffOp_add, hp, hq, map_add]
end Formalism.IncomingBounds.Cay
