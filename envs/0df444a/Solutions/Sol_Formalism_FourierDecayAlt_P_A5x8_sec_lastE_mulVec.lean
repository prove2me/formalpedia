-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lastE_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:54.974388+00:00
-- url     : https://prove2.me/submissions/ad61c546-e77c-4de2-bf9f-96f1aac21e40

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] {m N : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution {u : Matrix (Fin m) (Fin m) K} (hu : IsUpUni u) (η : Fin m → K) :
    lastE (u *ᵥ η) = lastE η := by
  unfold lastE
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [mulVec, dotProduct, Finset.sum_eq_single j]
    · rw [hu.2 j, one_mul]
    · intro k _ hk
      have hkj : k < j := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.isLt
        have : k.val ≠ j.val := fun h => hk (Fin.ext h)
        omega
      have h0 : u j k = 0 := hu.1 hkj
      rw [h0, zero_mul]
    · simp
  · rfl
end Formalism.FourierDecayAlt.P.A5x8
