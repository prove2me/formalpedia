-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.continuous_xi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:43.400577+00:00
-- url     : https://prove2.me/submissions/532d3c1d-f265-41bb-8b7a-d5683e2ce7d5

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
attribute [local instance] sfG sfW sfN sfW'
attribute [local instance] sfSS
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) :
    Continuous fun a : (ℝ × ℝ) × SS k r => xiTau D a.1 a.2 := by
  have h : Continuous fun a : (ℝ × ℝ) × SS k r =>
      (a.1.1 * lam k r D.z (Matrix.of a.2.1.2) - a.1.2 * lam k r D.z' (Matrix.of a.2.2.2)) :=
    (continuous_fst.fst.mul ((continuous_lam D.z).comp continuous_snd.fst.snd)).sub
      (continuous_fst.snd.mul ((continuous_lam D.z').comp continuous_snd.snd.snd))
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h))
end Formalism.FourierDecayAlt.P.B7
