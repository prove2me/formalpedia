-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.measurable_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:48:35.682495+00:00
-- url     : https://prove2.me/submissions/05c656e7-ae8c-493e-ba2e-68cd68a38c38

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_continuous_lam

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS
attribute [local instance] properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : Measurable fun a : (ℝ × ℝ) × SS k r => xiTau D a.1 a.2 := by
  have h : Measurable fun a : (ℝ × ℝ) × SS k r =>
      (a.1.1 * lam k r D.z (Matrix.of a.2.1.2) - a.1.2 * lam k r D.z' (Matrix.of a.2.2.2)) :=
    (measurable_fst.fst.mul ((continuous_lam D.z).measurable.comp measurable_snd.fst.snd)).sub
      (measurable_fst.snd.mul ((continuous_lam D.z').measurable.comp measurable_snd.snd.snd))
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp h))
end Formalism.FourierDecayAlt.P.B7
