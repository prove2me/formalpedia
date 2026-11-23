-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.isD_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:05.833803+00:00
-- url     : https://prove2.me/submissions/27048668-a759-4cec-9965-6315a1d3e44a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_mul_inv_one_up
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_inv
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
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) : IsD R k D⁻¹ := by
  refine ⟨isUpUni_inv K hD.1, isInt_inv R hD.2.1 (isUpUni_det K hD.1), fun a b ha => ?_⟩
  have h1 : (D * D⁻¹) a b = (1 : Matrix (Fin n) (Fin n) K) a b := by
    rw [mul_inv_one_up hD.1]
  rw [← h1, Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hD.2.2 a a ha, Matrix.one_apply_eq, one_mul]
  · intro l _ hl
    rw [hD.2.2 a l ha, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.A5x9
