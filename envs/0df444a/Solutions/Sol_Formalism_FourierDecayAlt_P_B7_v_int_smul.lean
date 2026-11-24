-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.v_int_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:22:50.474799+00:00
-- url     : https://prove2.me/submissions/7234669a-b8da-4521-bcd8-db35505b01da

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

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
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {u : P → E} (hu : Integrable u μ) {ξ : P → ℂ} (hξm : Measurable ξ) (hξ : ∀ p, ‖ξ p‖ = 1) :
    Integrable (fun p => ξ p • u p) μ := by
  refine hu.mono (hξm.aestronglyMeasurable.smul hu.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
  rw [norm_smul, hξ p, one_mul]
end Formalism.FourierDecayAlt.P.B7
