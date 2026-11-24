-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.Sd_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:38.172825+00:00
-- url     : https://prove2.me/submissions/e155657a-59f4-4ed1-b6a4-91160d2e2069

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_inv_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_UWset_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_first_coordinate_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_third_coordinate
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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ContinuousOn (fun p : SS k r => Sd D p) {p | D.inSS p} := by
  have h1 : ContinuousOn (fun p : SS k r => D.π (Matrix.of p.1.1)) {p | D.inSS p} :=
    D.π_cont.comp continuous_first_coordinate_matrix.continuousOn (fun p hp => hp.1)
  have h2 : ContinuousOn (fun p : SS k r => D.π' (Matrix.of p.2.1)⁻¹) {p | D.inSS p} :=
    D.π'_cont.comp ((inv_continuousOn k r).comp continuous_third_coordinate.continuousOn
      (fun p hp => UWset_sub _ _ _ hp.2.2.1)) (fun p hp => WeylGroupFacts.uw_inv hp.2.2.1)
  exact ((ContinuousLinearMap.compL ℂ Wq Wp Wp).continuous.comp_continuousOn h1).clm_comp
    (((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip).continuous.comp_continuousOn h2)
end Formalism.FourierDecayAlt.P.B6
