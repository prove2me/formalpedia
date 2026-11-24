-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B5.ae_inSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:34:59.844145+00:00
-- url     : https://prove2.me/submissions/3e4154c4-8466-4678-8493-8aa54e3def39

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_haar_ae

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B5
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  haveI := haar_sigmaFinite D.haarW
  haveI := haar_sigmaFinite D.haarN
  haveI := haar_sigmaFinite D.haarW'
  have h1 := haar_ae D.haarW
  have h2 := haar_ae D.haarN
  have h3 := haar_ae D.haarW'
  have a1 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW.prod D.μN),
      Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae h1).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have a2 : ∀ᵐ q : Mt k r × Mt k r ∂(D.μW'.prod D.μN),
      Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ QuantumDeterminants.Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae h3).and (Measure.quasiMeasurePreserving_snd.ae h2)
  have a3 := (Measure.quasiMeasurePreserving_fst (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a1
  have a4 := (Measure.quasiMeasurePreserving_snd (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN)).ae a2
  have a5 := a3.and a4
  unfold RealPlaceData.μSS
  filter_upwards [a5] with p hp
  unfold RealPlaceData.inSS
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
end Formalism.FourierDecayAlt.P.B5
