-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.sum_normSq_entries_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:29.333195+00:00
-- url     : https://prove2.me/submissions/f88692ee-62e7-4b48-856a-9d937adec3f0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_matrix_product_entry_bound

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
theorem _root_.solution (a b : Mat k r) : hilbertSchmidtNormSq (a * b) ≤ hilbertSchmidtNormSq a * hilbertSchmidtNormSq b := by
  unfold hilbertSchmidtNormSq
  calc ∑ i, ∑ j, Complex.normSq ((a * b) i j)
      ≤ ∑ i, ∑ j, (∑ l, Complex.normSq (a i l)) * ∑ l, Complex.normSq (b l j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => matrix_product_entry_bound a b i j
    _ = (∑ i, ∑ l, Complex.normSq (a i l)) * ∑ j, ∑ l, Complex.normSq (b l j) := by
        rw [Finset.sum_mul_sum]
    _ = (∑ i, ∑ l, Complex.normSq (a i l)) * ∑ l, ∑ j, Complex.normSq (b l j) := by
        rw [Finset.sum_comm (f := fun j l => Complex.normSq (b l j))]
end Formalism.FourierDecayAlt.P.B6
