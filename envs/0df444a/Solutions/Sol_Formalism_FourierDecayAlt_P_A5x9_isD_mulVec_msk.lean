-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.isD_mulVec_msk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:16.048829+00:00
-- url     : https://prove2.me/submissions/97df0b5b-b41e-4bfc-b02a-66d68ec3fd04

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
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
theorem _root_.solution {D : Matrix (Fin n) (Fin n) K} (hD : IsD R k D) (y : Fin n → K) :
    D *ᵥ msk k y = msk k (D *ᵥ y) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, msk]
  by_cases h : k < j.val
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k < l.val
    · rw [if_pos hl]
    · have : l < j := by rw [Fin.lt_def]; omega
      rw [up_zero hD.1 this, zero_mul, zero_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : k < l.val
    · have : j ≠ l := fun e => h (e ▸ hl)
      rw [hD.2.2 j l (by omega), Matrix.one_apply_ne this, zero_mul]
    · rw [if_neg hl, mul_zero]
end Formalism.FourierDecayAlt.P.A5x9
