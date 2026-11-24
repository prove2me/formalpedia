-- Prove2me | solution 1 for Formalism.REAL.frobenius_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:42:24.659863+00:00
-- url     : https://prove2.me/submissions/cd5cd62b-ae84-426e-8333-d55d2d8e7b6b

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_RightDerivativeZeroOutsideSupport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hs (A * B) ≤ hs A * hs B := by
  unfold hs
  have key : ∀ i j, ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    rw [Matrix.mul_apply]
    calc ‖∑ k, A i k * B k j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 := by
          gcongr
          calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
            _ = ∑ k, ‖A i k‖ * ‖B k j‖ := by simp only [norm_mul]
      _ ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2
        ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
          gcongr with i _ j _
          exact key i j
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
          rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ j, ‖A i j‖ ^ 2) * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
          congr 1
          exact Finset.sum_comm
end Formalism.REAL
