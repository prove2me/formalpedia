-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.ae_inSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:00.941556+00:00
-- url     : https://prove2.me/submissions/8d064f68-1f10-49c2-bd18-7db9008a7701

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_sigmaFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_haar_ae

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have := haar_sigmaFinite D.haarW
  have := haar_sigmaFinite D.haarN
  have := haar_sigmaFinite D.haarW'
  have h1 : ∀ᵐ p ∂D.μSS, (Matrix.of p.1.1 : Mat k r) ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae (haar_ae D.haarW)
  have h2 : ∀ᵐ p ∂D.μSS, (Matrix.of p.1.2 : Mat k r) ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae (haar_ae D.haarN)
  have h3 : ∀ᵐ p ∂D.μSS, (Matrix.of p.2.1 : Mat k r) ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae (haar_ae D.haarW')
  have h4 : ∀ᵐ p ∂D.μSS, (Matrix.of p.2.2 : Mat k r) ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae (haar_ae D.haarN)
  filter_upwards [h1, h2, h3, h4] with p a b c d
  exact ⟨a, b, c, d⟩
end Formalism.FourierDecayAlt.P.B6
