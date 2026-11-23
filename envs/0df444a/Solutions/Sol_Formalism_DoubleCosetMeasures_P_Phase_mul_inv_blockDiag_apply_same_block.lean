-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.mul_inv_blockDiag_apply_same_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:42.892056+00:00
-- url     : https://prove2.me/submissions/b35e2630-ea43-4e69-8be9-4b242469264a

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_low
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_bdiag_inv_blk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    {a c : Fin s.sum} (hac : blk s a = blk s c) :
    (x * (bdiag s x)⁻¹) a c = (1 : Matrix (Fin s.sum) (Fin s.sum) K) a c := by
  have hBinv := mul_inv_one_low (bdiag_low s hx)
  rw [← hBinv, Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hbc : blk s b = blk s c
  · rw [bdiag_apply s x a b, if_pos (hac.trans hbc.symm)]
  · rw [bdiag_inv_blk s hx hbc, mul_zero, mul_zero]
end Formalism.DoubleCosetMeasures.P.Phase
