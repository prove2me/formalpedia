-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.transferPart_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:35:41.202559+00:00
-- url     : https://prove2.me/submissions/9f067859-396d-406b-9cd9-8469d5d718fe

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_det
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_opNormAt_rowMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_opNormAt_colMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_htMap_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_log_bound
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_pi_ne_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_injOn
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_map_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap_injOn
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap_map_le
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_bot
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rkK_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open PrismTransfer
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (hMap : MapMu) (hPow : PowMu) : TransferPart := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A B n G x xs hA hB hA0 hn hG hxA hxsB hx1 hxs1 hinj hinj' hrk
  obtain ⟨p1, p2, _⟩ := hPow K V ι b X hX A n hA hA0 hn
  have hXn : ∀ v, IsUnit (Matrix.blockDiagonal' fun _ : Fin n => X v).det :=
    fun v => blockDiag_det (X v) (hX v)
  have hAn : (Submodule.pi Set.univ fun _ : Fin n => A).FG := Submodule.fg_pi fun _ => hA
  have hAn0 := pi_ne_bot hn A hA0
  have hrA : rkK A ≠ 0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0
  have hB0 : B ≠ ⊥ := by
    intro h
    rw [h, Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_bot] at hrk
    exact (Nat.mul_ne_zero hn.ne' hrA) hrk.symm
  obtain ⟨hb1, hb2⟩ := log_bound G n hG hn
  have d1 := hMap K (Fin n → V) (Σ _ : Fin n, ι) V ι (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X hXn hX (rowMap ((G : K) ^ 3) x)
    (Submodule.pi Set.univ fun _ : Fin n => A) B hAn hB hAn0 (rowMap_injOn G hG x A hinj)
    (rowMap_map_le G x A B hxA) (by rw [hrk, p1])
  have d2 := hMap K V ι (Fin n → V) (Σ _ : Fin n, ι) b X (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) hX hXn (colMap ((G : K) ^ 3) xs)
    B (Submodule.pi Set.univ fun _ : Fin n => A) hB hAn hB0 (colMap_injOn G hG xs B hinj')
    (colMap_map_le G xs A B hxsB) (by rw [hrk, p1])
  have e1 := htMap_le (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X (rowMap ((G : K) ^ 3) x) _ hb1
    (fun v => opNormAt_rowMap b X G x v fun i => hx1 i v)
  have e2 := htMap_le b X (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) (colMap ((G : K) ^ 3) xs) _ hb1
    (fun v => opNormAt_colMap b X hX G xs v fun i => hxs1 i v)
  rw [hb2] at e1 e2
  rw [p2] at d1 d2
  have h0 : degD b X B - (n : ℝ) * degD b X A =
      ((n : ℝ) * (rkK A : ℝ)) * (muDef b X B - muDef b X A) := by
    unfold degD
    rw [hrk]
    push_cast
    ring
  rw [h0, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * (rkK A : ℝ)), mul_comm]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) (by positivity)
end Formalism.BranchingDeterminantCap
