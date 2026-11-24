-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.aesm_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:34:59.167144+00:00
-- url     : https://prove2.me/submissions/b9446b86-c88f-4bd4-80f7-be9eb867b5a9

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_GV_closed

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution {μ : Measure (Mt k r)} (h : IsHaarOn (GV k r) μ) {f : Mat k r → E}
    (hf : ContinuousOn f (GV k r)) : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) μ := by
  have hc : IsClosed (X := Mt k r) (GV k r) := GV_closed
  have hs : MeasurableSet (α := Mt k r) (GV k r) := hc.measurableSet
  have hf' : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) (GV k r) := hf
  have h1 := hf'.aestronglyMeasurable (μ := μ) hs
  rwa [Measure.restrict_eq_self_of_ae_mem (haar_ae h)] at h1
end Formalism.FourierDecayAlt.P.B5
