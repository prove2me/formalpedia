-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.shf_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:18.012044+00:00
-- url     : https://prove2.me/submissions/3719989c-58f9-4c5b-b3a0-57a1970e5a47

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ξ β : Fin n → K) (h : β ⬝ᵥ ξ = 0) :
    (1 + vecMulVec ξ β)⁻¹ = 1 + vecMulVec (-ξ) β := by
  apply Matrix.inv_eq_right_inv
  have h2 : vecMulVec ξ β * vecMulVec ξ β = 0 := by
    rw [Matrix.mul_vecMulVec]
    have : vecMulVec ξ β *ᵥ ξ = 0 := by
      ext a
      simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, Pi.zero_apply]
      have : ∑ l, ξ a * β l * ξ l = ξ a * (β ⬝ᵥ ξ) := by
        simp only [dotProduct, Finset.mul_sum, mul_assoc]
      rw [this, h, mul_zero]
    rw [this]
    ext a b
    simp [vecMulVec_apply]
  have h3 : vecMulVec (-ξ) β = - vecMulVec ξ β := by
    ext a b
    simp [vecMulVec_apply]
  rw [h3, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_neg, h2]
  simp
end Formalism.FourierDecayAlt.P.A5x9
