-- Prove2me | solution 1 for Formalism.IncomingBounds.cayleyIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:41.730181+00:00
-- url     : https://prove2.me/submissions/5409a659-6695-4ca1-be1c-b404a8336a05

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_diffOp_one
import Theorems.Thm_Formalism_IncomingBounds_Cay_gen
import Theorems.Thm_Formalism_IncomingBounds_Cay_det_ne

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
open Formalism Formalism.IncomingBounds
open MvPolynomial Matrix
namespace Formalism.IncomingBounds
theorem _root_.solution : CayleyId := by
  intro F _ _ n0 s
  have hdl : detL F n0 = (Formalism.IncomingBounds.Cay.Mg F n0).det := rfl
  rw [hdl]
  cases n0 with
  | zero =>
    rw [Matrix.det_isEmpty, one_pow, one_pow, Formalism.IncomingBounds.Cay.diffOp_one, Finset.range_zero,
      Finset.prod_empty, one_smul]
  | succ k =>
    have h := Formalism.IncomingBounds.Cay.gen (K := F) (k+1) s k id id
    have hsub : (Formalism.IncomingBounds.Cay.Mg F (k+1)).submatrix id id =
        Formalism.IncomingBounds.Cay.Mg F (k+1) := Matrix.submatrix_id_id _
    have hadj : ((adjugate (Formalism.IncomingBounds.Cay.Mg F (k+1))).submatrix id id).det =
        (Formalism.IncomingBounds.Cay.Mg F (k+1)).det ^ k := by
      rw [Matrix.submatrix_id_id, det_adjugate, Fintype.card_fin, Nat.add_sub_cancel]
    rw [hsub, hadj] at h
    have hne : (Formalism.IncomingBounds.Cay.Mg F (k+1)).det ^ k ≠ 0 :=
      pow_ne_zero _ (Formalism.IncomingBounds.Cay.det_ne (K := F) (k+1))
    apply mul_left_cancel₀ hne
    rw [h, smul_eq_C_mul]
    ring
end Formalism.IncomingBounds
