-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_pairing_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:53.170839+00:00
-- url     : https://prove2.me/submissions/f4b8e668-57f7-4ef4-8d92-5c7a80dd096d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_hasDerivAt

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
theorem _root_.solution (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) {u v : ℝ → (Wq →L[ℂ] Wp)}
    {u' v' : Wq →L[ℂ] Wp} {y : ℝ} (hu : HasDerivAt u u' y) (hv : HasDerivAt v v' y) :
    HasDerivAt (fun s => hsInner (L (u s)) (v s)) (hsInner (L u') (v y) + hsInner (L (u y)) v') y := by
  have hLu : HasDerivAt (fun y => L (u y)) (L u') y :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt y hu
  exact hsInner_hasDerivAt hLu hv
end Formalism.FourierDecayAlt.P.B6
