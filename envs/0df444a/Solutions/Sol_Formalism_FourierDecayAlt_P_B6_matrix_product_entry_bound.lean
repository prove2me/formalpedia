-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.matrix_product_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:08:44.398964+00:00
-- url     : https://prove2.me/submissions/5f01b418-d22c-4efd-9a2e-a5adafd3afa5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (a b : Mat k r) (i j : Fin (2 * r + k + 1)) :
    Complex.normSq ((a * b) i j) ≤ (∑ l, Complex.normSq (a i l)) * ∑ l, Complex.normSq (b l j) := by
  rw [Matrix.mul_apply, Complex.normSq_eq_norm_sq]
  have h1 : ‖∑ l, a i l * b l j‖ ≤ ∑ l, ‖a i l‖ * ‖b l j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun l _ => norm_mul _ _
  have h2 : (∑ l, ‖a i l‖ * ‖b l j‖) ^ 2 ≤ (∑ l, ‖a i l‖ ^ 2) * ∑ l, ‖b l j‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ l, a i l * b l j‖ ^ 2 ≤ (∑ l, ‖a i l‖ * ‖b l j‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ l, ‖a i l‖ ^ 2) * ∑ l, ‖b l j‖ ^ 2 := h2
    _ = _ := by simp only [Complex.normSq_eq_norm_sq]
end Formalism.FourierDecayAlt.P.B6
