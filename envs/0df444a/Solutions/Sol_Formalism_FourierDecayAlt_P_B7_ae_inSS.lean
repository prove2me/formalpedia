-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.ae_inSS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:31.274866+00:00
-- url     : https://prove2.me/submissions/dd2d9f30-568c-46fa-a6ca-f92ccd47e9a6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  show ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p
  have q1 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.1 ∈ UWset k r D.z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae
      (ae_mem (by first | exact D.haarW | exact D.haarU | exact D.haarUW))
  have q2 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae
      (ae_mem (by first | exact D.haarN | exact D.haarNN))
  have q3 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.1 ∈ UWset k r D.z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae
      (ae_mem (by first | exact D.haarW' | exact D.haarU' | exact D.haarUW'))
  have q4 : ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae
      (ae_mem (by first | exact D.haarN | exact D.haarNN))
  filter_upwards [q1, q2, q3, q4] with p a b c d using ⟨a, b, c, d⟩
end Formalism.FourierDecayAlt.P.B7
