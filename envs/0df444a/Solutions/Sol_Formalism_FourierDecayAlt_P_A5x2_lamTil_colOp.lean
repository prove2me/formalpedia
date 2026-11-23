-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x2.lamTil_colOp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.421575+00:00
-- url     : https://prove2.me/submissions/2bb2f69f-68a7-4368-a3f1-13ee6400b642

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_row
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_big
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)
namespace Formalism.FourierDecayAlt.P.A5x2
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z.det) (m : Fin n → R) (c : Fin n)
    (hm : ∀ j, c.val ≤ j → lamTil R Z j m = 0) (j : ℕ) (hj : c.val ≤ j) :
    lamTil R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) j = lamTil R Z j := by
  by_cases hjn : j < n
  · apply LinearMap.ext
    intro v
    have hc : (Z⁻¹ *ᵥ coeLin R m) c = 0 := by rw [← lamTil_fin]; exact hm _ le_rfl
    have hjj : (Z⁻¹ *ᵥ coeLin R m) ⟨j, hjn⟩ = 0 := by rw [← lamTil_fin]; exact hm _ hj
    have e1 := lamTil_fin R (Z + vecMulVec (coeLin R m) (Pi.single c 1)) ⟨j, hjn⟩ v
    have e2 := lamTil_fin R Z ⟨j, hjn⟩ v
    simp only at e1 e2
    rw [e1, e2]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [colOp_row Z _ c hd hc, hjj, zero_mul, sub_zero]
  · rw [lamTil_big R _ j (by omega), lamTil_big R _ j (by omega)]
end Formalism.FourierDecayAlt.P.A5x2
