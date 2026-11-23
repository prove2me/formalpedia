-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_lastE_vecMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:49:51.491407+00:00
-- url     : https://prove2.me/submissions/6cee1668-a09a-4d11-a64c-43861889e48f

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
theorem _root_.solution {v : Matrix (Fin m) (Fin m) K} (hv : IsLowUni v) (ξ : Fin m → K) :
    lastE (ξ ᵥ* v) = lastE ξ := by
  unfold lastE
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with hj
  · rw [vecMul, dotProduct, Finset.sum_eq_single j]
    · rw [hv.2 j, mul_one]
    · intro k _ hk
      have hkj : k < j := by
        rw [Fin.lt_iff_val_lt_val]
        have := k.isLt
        have : k.val ≠ j.val := fun h => hk (Fin.ext h)
        omega
      have h0 : v k j = 0 := hv.1 hkj
      rw [h0, mul_zero]
    · simp
  · rfl
end Formalism.FourierDecayAlt.P.A5x8
