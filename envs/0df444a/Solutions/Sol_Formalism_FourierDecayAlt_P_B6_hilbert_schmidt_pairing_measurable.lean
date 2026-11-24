-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_pairing_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:06:05.982256+00:00
-- url     : https://prove2.me/submissions/e22de80a-b40d-42f0-9484-bdc09a3f5414

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hsInner_continuous

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
theorem _root_.solution {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) {a b : X → (Wq →L[ℂ] Wp)} (ha : AEStronglyMeasurable a μ)
    (hb : AEStronglyMeasurable b μ) : AEStronglyMeasurable (fun g => hsInner (L (a g)) (b g)) μ := by
  have h1 : AEStronglyMeasurable (fun g => L (a g)) μ := L.continuous.comp_aestronglyMeasurable ha
  have h2 : AEStronglyMeasurable (fun g => (L (a g), b g)) μ := h1.prodMk hb
  have h3 := (hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_aestronglyMeasurable h2
  exact h3
end Formalism.FourierDecayAlt.P.B6
