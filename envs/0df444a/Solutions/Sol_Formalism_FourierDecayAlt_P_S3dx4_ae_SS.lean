-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.ae_SS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:00:35.584842+00:00
-- url     : https://prove2.me/submissions/b16f1f2d-1e2a-4a6c-baf4-e0b763e82ac8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiRegOf
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MapInvMEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_ae_of_haarB
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haarW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq)
    [SigmaFinite D.μW] [SigmaFinite D.μN] [SigmaFinite D.μW'] :
    ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z ∧ Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r ∧
      Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' ∧ Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := ae_of_haarB D.haarW
  have hN := ae_of_haarB D.haarN
  have hW' := ae_of_haarB D.haarW'
  have e1 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hW)
  have e2 : ∀ᵐ p ∂D.μSS, Matrix.of p.1.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  have e3 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.1 ∈ Formalism.QuantumDeterminants.UWset k r D.z' :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hW')
  have e4 : ∀ᵐ p ∂D.μSS, Matrix.of p.2.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [e1, e2, e3, e4] with p h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩
end Formalism.FourierDecayAlt.P.S3dx4
