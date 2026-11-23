-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.msk_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:26.396777+00:00
-- url     : https://prove2.me/submissions/96b5be10-856a-4109-8de8-dce8cdd04a1a

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
theorem _root_.solution {p : Matrix (Fin n) (Fin n) K} (hp : IsUpUni p) (y : Fin n → K) :
    msk k (p *ᵥ y) = b22 k p *ᵥ msk k y := by
  ext j
  simp only [Matrix.mulVec, dotProduct, msk, b22]
  by_cases h : k < j.val
  · simp only [if_pos h]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : k < l.val
    · rw [if_pos hl]
    · have : l < j := by rw [Fin.lt_def]; omega
      rw [up_zero hp this, zero_mul, zero_mul]
  · simp only [if_neg h]
    symm
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : k < l.val
    · have : j ≠ l := fun e => h (e ▸ hl)
      rw [Matrix.one_apply_ne this, zero_mul]
    · rw [if_neg hl, mul_zero]
end Formalism.FourierDecayAlt.P.A5x9
