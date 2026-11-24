-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_wt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:11:41.534235+00:00
-- url     : https://prove2.me/submissions/cccd821c-aee6-487d-b959-d04510b1fded

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_ps_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_evGL_torus_TMat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] {B : Matrix κ κ (GLCoord ℤ n)}
  {be : κ → Fin n → ℤ} {Str : (Fin n → ℤ) → Finset (Fin n → ℤ)}
  {ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : nu ∈ Str mu)
    (K : TIdx mu) (k : κ) (I : TIdx nu) (h : ps mu nu (K, k) I ≠ 0) :
    qb_wtT mu K + be k = qb_wtT nu I := by
  have h1 := congrArg (evGL (torusPt n)) (qx_ps_equiv hd hmu hnu K k I)
  simp only [map_sum, map_mul, map_intCast, qb_evGL_torus_TMat, hd.2.1, Fintype.sum_prod_type,
    ite_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true,
    AddMonoidAlgebra.single_mul_single, one_mul] at h1
  by_contra hne
  have h2 := congrArg (fun x => x.coeff (qb_wtT nu I)) h1
  simp only [← zsmul_eq_mul', ← zsmul_eq_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul, if_neg hne, if_true, mul_zero, mul_one] at h2
  exact h h2.symm
end Formalism.InvariantFactorPaths.ColumnFamilies
