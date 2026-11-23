-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.bdiag_inv_blk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:18.733836+00:00
-- url     : https://prove2.me/submissions/59203f7d-5b5e-4428-876d-a425464c5326

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_low
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
section
set_option maxHeartbeats 400000
noncomputable section
open Matrix
namespace Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Phase
variable {K : Type} [CommRing K]
private lemma bdiag_apply (s : List ℕ) (x : Matrix (Fin s.sum) (Fin s.sum) K)
    (a c : Fin s.sum) : bdiag s x a c = if blk s a = blk s c then x a c else 0 := rfl
end Phase
end Formalism.DoubleCosetMeasures.P
end
end

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution (s : List ℕ) {x : Matrix (Fin s.sum) (Fin s.sum) K} (hx : IsLowUni x)
    {a c : Fin s.sum} (h : blk s a ≠ blk s c) : (bdiag s x)⁻¹ a c = 0 := by
  have hBinv : bdiag s x * (bdiag s x)⁻¹ = 1 := mul_inv_one_low (bdiag_low s hx)
  have hP : bdiag s x * bdiag s (bdiag s x)⁻¹ = 1 := by
    ext a' c'
    have h1 := congrFun (congrFun hBinv a') c'
    rw [Matrix.mul_apply] at h1
    rw [Matrix.mul_apply]
    by_cases hac : blk s a' = blk s c'
    · rw [← h1]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : blk s a' = blk s b
      · rw [bdiag_apply s ((bdiag s x)⁻¹), if_pos (hab.symm.trans hac)]
      · rw [bdiag_apply s x, if_neg hab, zero_mul, zero_mul]
    · rw [Matrix.one_apply_ne (fun h' => hac (by rw [h']))]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hab : blk s a' = blk s b
      · rw [bdiag_apply s ((bdiag s x)⁻¹), if_neg (fun h' => hac (hab.trans h')), mul_zero]
      · rw [bdiag_apply s x, if_neg hab, zero_mul]
  rw [Matrix.inv_eq_right_inv hP, bdiag_apply, if_neg h]
end Formalism.DoubleCosetMeasures.P.Phase
