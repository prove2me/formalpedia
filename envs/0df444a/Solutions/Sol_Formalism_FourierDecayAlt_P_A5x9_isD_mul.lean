-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.isD_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:15.583807+00:00
-- url     : https://prove2.me/submissions/555870be-4e86-4bc7-bf5d-f9f88fa425ad

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_mul
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
theorem _root_.solution {D E : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (hE : IsD R k E) :
    IsD R k (D * E) := by
  refine ⟨isUpUni_mul K hD.1 hE.1, isInt_mul R hD.2.1 hE.2.1, fun a b ha => ?_⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · rw [hD.2.2 a a ha, Matrix.one_apply_eq, one_mul, hE.2.2 a b ha]
  · intro l _ hl
    rw [hD.2.2 a l ha, Matrix.one_apply_ne (Ne.symm hl), zero_mul]
  · simp
end Formalism.FourierDecayAlt.P.A5x9
