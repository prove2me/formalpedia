-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Sd_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:27:52.504137+00:00
-- url     : https://prove2.me/submissions/4f01dadc-4668-4d3c-bb80-c9971e6540ae

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Sd_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_opNorm_le_one_of_norm_map_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv


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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) (X : Wq →L[ℂ] Wp) :
    ‖Sd D p X‖ ≤ ‖X‖ := by
  rw [Sd_apply]
  have h1 : ‖D.π (Matrix.of p.1.1)‖ ≤ 1 := opNorm_le_one_of_norm_map_eq _ (D.π_unitary _ hp.1)
  have h2 : ‖D.π' (Matrix.of p.2.1)⁻¹‖ ≤ 1 := opNorm_le_one_of_norm_map_eq _ (D.π'_unitary _ (WeylGroupFacts.uw_inv hp.2.2.1))
  calc _ ≤ ‖D.π (Matrix.of p.1.1)‖ * ‖X.comp (D.π' (Matrix.of p.2.1)⁻¹)‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * (‖X‖ * ‖D.π' (Matrix.of p.2.1)⁻¹‖) :=
        mul_le_mul h1 (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _) zero_le_one
    _ ≤ 1 * (‖X‖ * 1) := by gcongr
    _ = ‖X‖ := by ring
end Formalism.FourierDecayAlt.P.B6
