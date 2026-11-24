-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hsInner_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:21:20.549359+00:00
-- url     : https://prove2.me/submissions/2d2561c7-2d95-4b04-b392-027ff56c82e7

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hilbert_schmidt_inner_basis_sum

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (A B : Wq →L[ℂ] Wp) : ‖hsInner A B‖ ≤ (Module.finrank ℂ Wq : ℝ) * ‖A‖ * ‖B‖ := by
  rw [hilbert_schmidt_inner_basis_sum]
  calc ‖∑ i, inner ℂ (B (stdOrthonormalBasis ℂ Wq i)) (A (stdOrthonormalBasis ℂ Wq i))‖
      ≤ ∑ i : Fin (Module.finrank ℂ Wq), ‖A‖ * ‖B‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        have h1 : ‖B (stdOrthonormalBasis ℂ Wq i)‖ ≤ ‖B‖ := by
          simpa using B.le_opNorm (stdOrthonormalBasis ℂ Wq i)
        have h2 : ‖A (stdOrthonormalBasis ℂ Wq i)‖ ≤ ‖A‖ := by
          simpa using A.le_opNorm (stdOrthonormalBasis ℂ Wq i)
        calc _ ≤ ‖B (stdOrthonormalBasis ℂ Wq i)‖ * ‖A (stdOrthonormalBasis ℂ Wq i)‖ := norm_inner_le_norm _ _
          _ ≤ ‖B‖ * ‖A‖ := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
          _ = ‖A‖ * ‖B‖ := mul_comm _ _
    _ = (Module.finrank ℂ Wq : ℝ) * ‖A‖ * ‖B‖ := by
        simp [mul_assoc]
end Formalism.FourierDecayAlt.P.B6
