-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.norm_product_continuous_on
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:47:59.54613+00:00
-- url     : https://prove2.me/submissions/45864958-fd33-438f-8176-1f7ff6261c30

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_gN_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inSS_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_first_coordinate_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_matrix_coordinate_projection
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_third_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_fourth_coordinate
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_matrix_mul

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
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ContinuousOn (normProductOfPair (k := k) (r := r)) {p | D.inSS p} := by
  unfold normProductOfPair
  have h1 : ContinuousOn (fun p : SS k r => (Matrix.of p.1.2 * Matrix.of p.1.1 : Mat k r)) {p | D.inSS p} :=
    continuousOn_matrix_mul continuous_matrix_coordinate_projection.continuousOn continuous_first_coordinate_matrix.continuousOn
  have h2 : ContinuousOn (fun p : SS k r => (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)) {p | D.inSS p} :=
    continuousOn_matrix_mul continuous_fourth_coordinate.continuousOn continuous_third_coordinate.continuousOn
  have h3 : ContinuousOn (fun p : SS k r => (Matrix.of p.2.2 * Matrix.of p.2.1 : Mat k r)⁻¹) {p | D.inSS p} :=
    (inv_continuousOn k r).comp h2 (fun p hp => (inSS_mem D hp).2)
  exact (gN_continuous.comp_continuousOn h1).mul (gN_continuous.comp_continuousOn h3)
end Formalism.FourierDecayAlt.P.B6
