-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qx_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:15.447443+00:00
-- url     : https://prove2.me/submissions/927bd450-8048-42d7-bef0-799085e4c361

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxPhApply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_ps_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qx_ph_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_equiv_apply


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
variable {M M' : GLMod n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hd : IsStripData B be Str ps) (e : M'.ι ≃ M.ι × κ) (hT : IsTensor M M' B e) (CF : ColFam M)
    (x : qx_J Str CF) (i : M'.ι) (I : TIdx (x.2 : Fin n → ℤ)) :
    ∑ k, M'.A i k * (qx_ph ps e CF x k I : GLCoord ℤ n) =
      ∑ I', (qx_ph ps e CF x i I' : GLCoord ℤ n) * TMat (x.2 : Fin n → ℤ) I' I := by
  obtain ⟨j, nu, hnu⟩ := x
  have hmu := CF.dom j
  have hT' : ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2 := hT
  simp only [qx_ph_apply, hT', Int.cast_sum, Int.cast_mul]
  rw [← e.symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  calc ∑ m, ∑ k, M.A (e i).1 m * B (e i).2 k *
        ∑ K, (CF.ph j m K : GLCoord ℤ n) * (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)
      = ∑ K, ∑ k, (∑ m, M.A (e i).1 m * (CF.ph j m K : GLCoord ℤ n)) * (B (e i).2 k *
          (ps (CF.mu j) nu (K, k) I : GLCoord ℤ n)) := by
        simp only [mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        refine sum_congr rfl fun K _ => sum_congr rfl fun k _ => sum_congr rfl fun m _ => by ring
    _ = ∑ K', (CF.ph j (e i).1 K' : GLCoord ℤ n) * ∑ y : TIdx (CF.mu j) × κ,
          TMat (CF.mu j) K' y.1 * B (e i).2 y.2 * (ps (CF.mu j) nu y I : GLCoord ℤ n) := by
        simp only [qb_equiv_apply, Fintype.sum_prod_type, mul_sum, sum_mul]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        rw [sum_comm]
        conv_lhs => enter [2, k]; rw [sum_comm]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun K _ => sum_congr rfl fun k _ => by ring
    _ = _ := by
        simp only [qx_ps_equiv hd hmu hnu, mul_sum, sum_mul]
        rw [sum_comm]
        refine sum_congr rfl fun I' _ => sum_congr rfl fun K _ => by ring
end Formalism.InvariantFactorPaths.ColumnFamilies
